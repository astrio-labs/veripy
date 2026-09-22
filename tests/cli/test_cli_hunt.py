def test_emit_rejects_same_stem_inputs(tmp_path, capsys):
    from veripy.cli import cmd_emit

    a = tmp_path / "a"
    b = tmp_path / "b"
    a.mkdir()
    b.mkdir()
    src = "#@ ensures result == x\ndef f(x: int) -> int:\n    return x\n"
    (a / "foo.py").write_text(src)
    (b / "foo.py").write_text(src)
    status = cmd_emit([a / "foo.py", b / "foo.py"], tmp_path / "out")
    err = capsys.readouterr().err
    assert status == 1
    assert "collision" in err
    assert not (tmp_path / "out" / "foo_checked.py").exists()
