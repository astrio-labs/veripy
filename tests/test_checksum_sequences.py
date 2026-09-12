from pathlib import Path
import pytest
from veripy.backends.dafny.encoder import encode_module,EncodeError
from veripy.frontend.extract import parse_source
from veripy.difftest.harness import difftest_file
from veripy.backends.dafny.driver import find_dafny


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
@pytest.mark.parametrize('body',[
 'return xs[1::2]', 'return xs[-5:99:3]',
])
def test_positive_stride_preserves_python_slicing(tmp_path,body):
    p=tmp_path/'stride.py';p.write_text('#@ ensures True\ndef f(xs: list[int]) -> list[int]:\n    '+body+'\n')
    result=difftest_file(p,tmp_path/'diff',examples=60)
    assert result.ok,result


def test_immutable_tuple_does_not_become_a_list():
    prefix='#@ ensures True\ndef f(xs: list[int]) -> bool:\n    values = tuple(x for x in xs)\n'
    for suffix in ['    return values == xs\n', '    values.append(1)\n    return True\n']:
        with pytest.raises(EncodeError):encode_module(prefix+suffix,parse_source(prefix+suffix),'bad.py')


def test_iterator_cannot_escape_and_be_reused():
    s='#@ ensures True\ndef f(s: str) -> int:\n    it = reversed(s)\n    return 0\n'
    with pytest.raises(EncodeError):encode_module(s,parse_source(s),'bad.py')
