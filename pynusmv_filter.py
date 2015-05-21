import pynusmv
from pynusmv.nusmv.parser import parser
import copy
import pynusmv_formula

# Filter function
# Will pick up one of the functions below according to the first argument
def filter(filter_type, spec):
    if (filter_type == 'ALL') | (filter_type == 'all'):
        return all(spec)
    elif (filter_type == 'AF') | (filter_type == 'af'):
        return af(spec)
    elif (filter_type == 'IFF') | (filter_type == 'iff'):
        return iff(spec)
    else:
        return None

# Choose all the sub-formulas
# Return the list containing all the positions of sub-formulas
def all(spec, actual_pos = []):
    result = []
    if spec != None:
        result.append(actual_pos)
        if (spec.type == parser.NOT) | (spec.type == parser.EX) | (spec.type == parser.EF) | (spec.type == parser.EG) | (spec.type == parser.AX) | (spec.type == parser.AF) | (spec.type == parser.AG):
            t1 = copy.copy(actual_pos)
            t1.append(1)
            result.extend(all(spec.car, t1))
        elif (spec.type == parser.OR) | (spec.type == parser.AND) | (spec.type == parser.IMPLIES) | (spec.type == parser.IFF) | (spec.type == parser.EU) | (spec.type == parser.EW) | (spec.type == parser.AU) | (spec.type == parser.AW):
            t1 = copy.copy(actual_pos)
            t1.append(1)
            result.extend(all(spec.car, t1))
            t2 = copy.copy(actual_pos)
            t2.append(2)
            result.extend(all(spec.cdr, t2))
    return result

# Choose all the AF
# Return the list containing all the positions of AF sub-formulas
def af(spec):
    def af_sub_formulas_check(spec, af_sf, act = []):
        if spec != None:
            if spec.type == parser.AF:
                af_sf.append(copy.copy(act))
            if pynusmv_formula.is_comp_type(spec):
                left_act = copy.copy(act)
                left_act.append(1)
                af_sub_formulas_check(spec.car, af_sf, left_act)
                right_act = copy.copy(act)
                right_act.append(2)
                af_sub_formulas_check(spec.cdr, af_sf, right_act)

    af_sf = []
    af_sub_formulas_check(spec, af_sf)
    return af_sf

# Choose all the IFF
# Return the list containing all the positions of IFF sub-formulas
def iff(spec):
    # Find out all the iff sub-formulas
    # iff_sf is the list containing all the iff sub-formulas
    # All the sub-formulas are presented by their positions in the formula
    def iff_sub_formulas_check(spec, iff_sf, act = []):
        if spec != None:
            if spec.type == parser.IFF:
                iff_sf.append(copy.copy(act))
            if pynusmv_formula.is_comp_type(spec):
                left_act = copy.copy(act)
                left_act.append(1)
                iff_sub_formulas_check(spec.car, iff_sf, left_act)
                right_act = copy.copy(act)
                right_act.append(2)
                iff_sub_formulas_check(spec.cdr, iff_sf, right_act)

    iff_sf = []
    iff_sub_formulas_check(spec, iff_sf)
    return iff_sf