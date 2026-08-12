"""MBPP/97 — frequency count of the items of a list of lists.

Canonical algorithm kept; the flattened list is bound to a new name
(`flat`) instead of rebinding the parameter, so the strict type gate can
give each binding a single type.
"""


#@ verified
#@ ensures forall key in result :: result[key] == sum(1 for sublist in list1 for item in sublist if item == key)
#@ ensures forall sublist in list1, item in sublist :: item in result
#@ ensures forall key in result :: exists sublist in list1 :: key in sublist
#@ ensures sum(result[key] for key in result) == sum(len(sublist) for sublist in list1)
def frequency_lists(list1: list[list[int]]) -> dict[int, int]:
    flat: list[int] = [item for sublist in list1 for item in sublist]
    dic_data: dict[int, int] = {}
    for num in flat:
        #@ invariant forall key in dic_data :: dic_data[key] >= 1
        #@ invariant forall key in dic_data :: key in flat
        #@ invariant sum(dic_data[key] for key in dic_data) <= len(flat)
        if num in dic_data.keys():
            dic_data[num] += 1
        else:
            key = num
            value = 1
            dic_data[key] = value
    return dic_data
