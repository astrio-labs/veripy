import json
from pathlib import Path
import tempfile
import unittest

from veripy.native_repair import repair_native, NativeEngineError


def observation(ok=False, guard=True, bypass=True):
    return dict(guard={'ok':guard}, upstream_checks={'no_avoid_verify':bypass},
                verification={'ok':ok, 'timeout':False})


class Adapter:
    def __init__(self, initial_ok=False, pruning_success=False):
        self.initial_ok = initial_ok
        self.pruning_success = pruning_success
        self.budgets=[]
    def assess(self, source, folder):
        return observation(source=='good' or (source=='original' and self.initial_ok))
    def accepted(self, o):
        return o['guard']['ok'] and o['upstream_checks']['no_avoid_verify'] and o['verification']['ok'] and not o['verification']['timeout']
    def feedback(self, o, mode):
        return mode+' failure'
    def prune(self, source, o, folder, budget):
        self.budgets.append(budget)
        r=dict(accepted=False, attempts=[observation()], verifier_calls=1, verifier_seconds=.1)
        if self.pruning_success:
            folder.mkdir(parents=True); p=folder/'candidate.dfy'; p.write_text('good')
            r.update(accepted=True, candidate=str(p), attempts=[observation(True)])
        return r


class NativeRepairTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)/'run'
        self.requests=[]
    def tearDown(self): self.tmp.cleanup()
    def engine(self, request, step):
        self.requests.append(request)
        return 'generated bad'
    def test_preflight_success_skips_model_and_pruning(self):
        a=Adapter(initial_ok=True)
        r=repair_native('original',self.root,a,self.engine)
        self.assertEqual(r['status'],'input_already_verified')
        self.assertEqual(self.requests,[]);self.assertEqual(a.budgets,[])
    def test_pruning_success_stops_before_next_model_call(self):
        a=Adapter(pruning_success=True)
        r=repair_native('original',self.root,a,self.engine)
        self.assertTrue(r['success']);self.assertEqual(len(self.requests),1)
        self.assertEqual(Path(r['candidate']).read_text(),'good')
    def test_failed_pruning_keeps_generated_candidate_and_total_cap(self):
        a=Adapter()
        r=repair_native('original',self.root,a,self.engine,max_responses=4,pruning_budget=2)
        self.assertEqual(a.budgets,[2,1]);self.assertEqual(r['pruning_variants'],2)
        self.assertEqual(self.requests[1]['history'][0]['candidate'],'generated bad')
        self.assertFalse(r['success']);self.assertEqual(r['responses'],4)
    def test_shared_initial_counts_in_response_cap_without_dispatch(self):
        r=repair_native('original',self.root,Adapter(),self.engine,max_responses=2,pruning_budget=0,
                        initial=('shared bad',observation()),preflight=observation())
        self.assertEqual(len(self.requests),1);self.assertEqual(r['responses'],2)
        self.assertEqual(self.requests[0]['history'][0]['candidate'],'shared bad')
    def test_input_bypass_stops_before_model(self):
        r=repair_native('original',self.root,Adapter(),self.engine,preflight=observation(True,bypass=False))
        self.assertFalse(r['success']);self.assertEqual(self.requests,[])
    def test_engine_failure_records_and_does_not_retry(self):
        def fail(request,step): raise NativeEngineError('timeout')
        r=repair_native('original',self.root,Adapter(),fail)
        self.assertEqual(r['status'],'engine_failure');self.assertEqual(r['model_dispatches'],1)
        self.assertEqual(json.loads((self.root/'result.json').read_text())['engine_error'],'timeout')
    def test_output_overwrite_refused(self):
        self.root.mkdir()
        with self.assertRaises(FileExistsError):repair_native('original',self.root,Adapter(),self.engine)
    def test_false_pruning_success_rejected(self):
        class Bad(Adapter):
            def prune(self,*args,**kwargs):
                return dict(accepted=True,attempts=[observation()],verifier_calls=1,verifier_seconds=0)
        with self.assertRaisesRegex(RuntimeError,'unverified'):
            repair_native('original',self.root,Bad(),self.engine)

if __name__=='__main__':unittest.main()
