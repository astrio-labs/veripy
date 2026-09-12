"""Mutable bytearrays, permitted aliases, and checked output-state contracts."""
from pathlib import Path
import pytest
from veripy.api import verify,guard
from veripy.backends.dafny.driver import find_dafny
from veripy.backends.dafny.buffers import encode_buffers
from veripy.backends.dafny.encoder import EncodeError
from veripy.frontend.extract import parse_source
from veripy.guards.runtime import PreconditionError

SOURCE='''#@ requires allow_buffer_alias("result", "scanline")
#@ requires len(scanline) == len(buffer("result")) and len(scanline) > 0
#@ ensures buffer("result")[0] == (old_buffer("scanline")[0] + 1) % 256
def increment(scanline: bytearray, previous: bytearray, result: bytearray) -> None:
    buffer_result = 1
    result[0] = scanline[0] + buffer_result & 255
'''


def test_buffer_policy_is_mandatory():
    s=SOURCE.replace('#@ requires allow_buffer_alias("result", "scanline")\n','')
    with pytest.raises(EncodeError,match='policy'):encode_buffers(s,parse_source(s),'bad.py')


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
def test_mutation_and_alias_policy_verify_and_guard(tmp_path):
    p=tmp_path/'buffer.py';p.write_text(SOURCE)
    result=verify(p,tmp_path/'proof',backend='dafny-buffers')
    assert result['status']=='ok',result
    emitted=guard(p,backend='dafny-buffers',check_ensures=True);assert emitted['ok'],emitted
    ns={};exec(emitted['source'],ns)
    a=bytearray([255]);b=bytearray([0]);c=bytearray([6])
    assert ns['increment'](a,b,c) is None
    assert c==bytearray([0]) and a==bytearray([255])
    assert ns['increment'](a,b,a) is None and a==bytearray([0])
    before=bytes(b)
    with pytest.raises(PreconditionError,match='alias policy'):ns['increment'](a,b,b)
    assert bytes(b)==before


@pytest.mark.skipif(find_dafny() is None,reason='Dafny required')
def test_out_of_byte_range_write_cannot_verify(tmp_path):
    s=SOURCE.replace('scanline[0] + buffer_result & 255','300')
    p=tmp_path/'bad.py';p.write_text(s)
    assert verify(p,tmp_path/'proof',backend='dafny-buffers')['status']=='failed'
