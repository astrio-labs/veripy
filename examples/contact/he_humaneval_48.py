"""HumanEval 48: check whether a string is a palindrome."""


#@ verified
#@ ensures result == (forall i in range(len(text)) :: text[i] == text[len(text) - 1 - i])
def is_palindrome(text: str) -> bool:
    for i in range(len(text)):
        #@ invariant 0 <= i < len(text)
        #@ invariant forall k in range(i) :: text[k] == text[len(text) - 1 - k]
        if text[i] != text[len(text) - 1 - i]:
            return False
    return True
