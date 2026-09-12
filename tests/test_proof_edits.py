from pathlib import Path
import tempfile
import unittest
from veripy.proof_edits import compile_plan, anchor_catalog, source_hash, EditPlanError
from veripy.proof_diagnostics import diagnostic_experiments
from veripy.native_repair import repair_native, NativeProposalError
from test_native_repair import Adapter, observation

class EditTests(unittest.TestCase):
    def setUp(self):
        self.source='// 😀\nmethod M() { assert true; }'
        start=len(self.source[:self.source.index('assert')].encode())
        self.catalog=anchor_catalog(self.source,[dict(kind='statement',start=start,offset=start)])
    def plan(self,edits):return dict(original_sha256=source_hash(self.source),edits=edits)
    def edit(self,text='assert false;'):return dict(id='A1',op='assert_before',target='S1',text=text)
    def test_unicode_original_bytes_and_replacing_plan(self):
        candidate=compile_plan(self.source,self.catalog,self.plan([self.edit()]))
        self.assertEqual(candidate.replace('\nassert false;\n',''),self.source)
        self.assertEqual(compile_plan(self.source,self.catalog,self.plan([])),self.source)
    def test_stale_source_and_duplicate_ids_rejected(self):
        plan=self.plan([]);plan['original_sha256']='old'
        with self.assertRaises(EditPlanError):compile_plan(self.source,self.catalog,plan)
        with self.assertRaises(EditPlanError):compile_plan(self.source,self.catalog,self.plan([self.edit(),self.edit()]))
    def test_arbitrary_replacement_and_wrong_target_rejected(self):
        edit=self.edit();edit['op']='replace_source'
        with self.assertRaises(EditPlanError):compile_plan(self.source,self.catalog,self.plan([edit]))
        edit=self.edit();edit['target']='END'
        with self.assertRaises(EditPlanError):compile_plan(self.source,self.catalog,self.plan([edit]))
    def test_malformed_proposal_consumes_response_then_recovers(self):
        with tempfile.TemporaryDirectory() as tmp:
            calls=[]
            def engine(request,step):
                calls.append(request)
                if len(calls)==1:raise NativeProposalError('bad schema','{}')
                return 'good'
            r=repair_native('original',Path(tmp)/'run',Adapter(),engine,max_responses=2)
            self.assertTrue(r['success']);self.assertEqual(r['proposal_rejections'],1)
            self.assertIn('bad schema',calls[1]['history'][0]['feedback'])
    def test_probe_summary_does_not_label_timeout_as_progress(self):
        o=observation();o['verification']['diagnostics']=[]
        trial=observation();trial['verification'].update(timeout=True,diagnostics=[])
        trial['removed']=[dict(start=0,end=5,kind='AssertStmt')]
        r=diagnostic_experiments('assert false;',o,[trial])
        self.assertEqual(r['deletion_experiments'][0]['outcome']['status'],'timeout')
        self.assertIn('not proof progress',r['interpretation'])

if __name__=='__main__':unittest.main()
