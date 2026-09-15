"""Relational admission must preserve dependency and Python calling semantics."""
import pytest
from veripy.compatibility import compare
from veripy.backends.dafny.driver import find_dafny

DAFNY=pytest.mark.skipif(not find_dafny(),reason='Dafny required')

def pair(tmp_path,old,new=None,**kwargs):
    a=tmp_path/'old.py';b=tmp_path/'new.py'
    a.write_text(old);b.write_text(new if new is not None else old)
    return compare(a,b,tmp_path/'proof',time_limit=20,**kwargs)

@DAFNY
def test_constant_environments_are_independently_checked(tmp_path):
    source='OFFSET=3\n#@ ensures result == x + OFFSET\ndef f(x:int)->int:\n return x+OFFSET\n'
    result=pair(tmp_path,source)
    assert result['status']=='proved-compatible',result
    assert result['environments'][0]['constants']=={'OFFSET':3}

@DAFNY
def test_changed_constant_cannot_share_the_old_environment(tmp_path):
    source='OFFSET=3\n#@ ensures result == x + OFFSET\ndef f(x:int)->int:\n return x+OFFSET\n'
    result=pair(tmp_path,source,source.replace('OFFSET=3','OFFSET=4'))
    assert result['status']=='inconclusive',result
    assert not result['proof']['ok']

@DAFNY
def test_matching_defaults_and_keywords_are_proved(tmp_path):
    result=pair(tmp_path,'#@ ensures result == x + offset\ndef f(x:int=2,*,offset:int=3)->int:\n return x+offset\n')
    assert result['status']=='proved-compatible',result
    assert result['replay']['admitted_samples']>0

@DAFNY
def test_keyword_replay_uses_python_binding(tmp_path):
    old='#@ ensures result == x\ndef f(*,x:int=2)->int:\n return x\n'
    new=old.replace('result == x','result == x+1').replace('return x','return x+1')
    result=pair(tmp_path,old,new)
    assert result['status']=='behavioral-difference',result
    assert result['witness']['old'].get('return') is not None

@pytest.mark.parametrize('old,new', [('2','3'),('True','1'),('2','len([])')])
def test_changed_or_executable_defaults_are_not_ignored(tmp_path,old,new):
    source='#@ ensures result == x\ndef f(x:int=DEFAULT)->int:\n return x\n'
    assert pair(tmp_path,source.replace('DEFAULT',old),source.replace('DEFAULT',new))['status']=='unsupported'

@pytest.mark.parametrize('default',['None','True','"2"'])
def test_same_out_of_domain_default_is_not_a_vacuous_proof(tmp_path,default):
    source=f'#@ ensures result == x\ndef f(x:int={default})->int:\n return x\n'
    result=pair(tmp_path,source)
    assert result['status']=='unsupported' and 'parameter type' in result['reason']

@DAFNY
def test_named_exception_outcomes_compare_tags_and_returns(tmp_path):
    source='''class Invalid(ValueError): pass
#@ ensures raised("Invalid") == (x < 0)
#@ ensures raised() == (x < 0)
#@ ensures not raised() ==> result == x
def f(x:int)->int:
 if x < 0: raise Invalid()
 return x
'''
    result=pair(tmp_path,source,backend='dafny-outcomes')
    assert result['status']=='proved-compatible',result
    text=(tmp_path/'proof/comparison.dfy').read_text()
    assert 'if oldError == 0' in text

def test_exception_hierarchy_change_is_not_equal_integer_tags(tmp_path):
    source='class Invalid(ValueError): pass\n#@ ensures True\ndef f(x:int)->int:\n return x\n'
    result=pair(tmp_path,source,source.replace('Invalid','Other'),backend='dafny-outcomes')
    assert result['status']=='unsupported' and 'hierarchy' in result['reason']

@pytest.mark.parametrize('prefix',['from unknown import thing\n','OFFSET = open("never-read")\n'])
def test_dependency_admission_never_executes_arbitrary_initialization(tmp_path,prefix):
    result=pair(tmp_path,prefix+'#@ ensures result == x\ndef f(x:int)->int:\n return x\n')
    assert result['status']=='unsupported'
