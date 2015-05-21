import pynusmv
from pynusmv.nusmv.parser import parser
import copy

# Function that determines if the type of SPEC is a compositional one
def is_comp_type(spec):
    if spec == None:
        return False
    elif spec.type == parser.NOT:
        return True
    elif spec.type == parser.OR:
        return True
    elif spec.type == parser.AND:
        return True
    elif spec.type == parser.IMPLIES:
        return True
    elif spec.type == parser.IFF:
        return True
    elif spec.type == parser.EX:
        return True
    elif spec.type == parser.EF:
        return True
    elif spec.type == parser.EG:
        return True
    elif spec.type == parser.EU:
        return True
    elif spec.type == parser.EW:
        return True
    elif spec.type == parser.AX:
        return True
    elif spec.type == parser.AF:
        return True
    elif spec.type == parser.AG:
        return True
    elif spec.type == parser.AU:
        return True
    elif spec.type == parser.AW:
        return True
    else:
        return False

# Create a new compositional spec with a given type
def create_comp(type, left, right = None):
    if type == parser.NOT:
        return pynusmv.prop.not_(left)
    elif type == parser.OR:
        return pynusmv.prop.or_(left, right)
    elif type == parser.AND:
        return pynusmv.prop.and_(left, right)
    elif type == parser.IMPLIES:
        return pynusmv.prop.imply(left, right)
    elif type == parser.IFF:
        return pynusmv.prop.iff(left, right)
    elif type == parser.EX:
        return pynusmv.prop.ex(left)
    elif type == parser.EF:
        return pynusmv.prop.ef(left)
    elif type == parser.EG:
        return pynusmv.prop.eg(left)
    elif type == parser.EU:
        return pynusmv.prop.eu(left, right)
    elif type == parser.EW:
        return pynusmv.prop.ew(left, right)
    elif type == parser.AX:
        return pynusmv.prop.ax(left)
    elif type == parser.AF:
        return pynusmv.prop.af(left)
    elif type == parser.AG:
        return pynusmv.prop.ag(left)
    elif type == parser.AU:
        return pynusmv.prop.au(left, right)
    elif type == parser.AW:
        return pynusmv.prop.aw(left, right)
    else:
        return None

# Copy of a spec
def spec_copy(spec):
    if spec == None:
        return None
    elif is_comp_type(spec):
        return create_comp(spec.type, spec_copy(spec.car), spec_copy(spec.cdr))
    else:
        return pynusmv.prop.atom(str(spec))

# Replacement of a sub-formula of given position (pos) by a new formula (newf) in the formula (spec)
# And return the new formula
def replace(spec, pos, newf):
    p = copy.copy(pos)
    if len(p) == 0:
        return spec_copy(newf)
    elif p[0] == 1: # go left
        del p[0]
        return create_comp(spec.type, replace(spec.car, p, spec_copy(newf)), spec_copy(spec.cdr))
    elif p[0] == 2: # go right
        del p[0]
        return create_comp(spec.type, spec_copy(spec.car), replace(spec.cdr, p, spec_copy(newf)))
    else: # error
        return None

# Find a sub-formula according to a given position (pos) in the formula (spec)
# Position = List containing the trace
# 1 = left
# 2 = right
def find_sub_spec(spec, pos):
    p = copy.copy(pos)
    if len(p) == 0:
        return spec
    elif p[0] == 1:
        del p[0]
        return find_sub_spec(spec.car, p)
    elif p[0] == 2:
        del p[0]
        return find_sub_spec(spec.cdr, p)

# Polarity of a sub-formula
# Pre-condition: M |= the formula (spec)
# Return False if the sub-formula (sf) is of positive polarity in the formula (spec)
# Return True if the sub-formula (sf) is of negative polarity in the formula (spec)
# The sub-formulas is presented by its position in the formula
def polarity(spec, sf):
    act = spec
    polarity = 1
    for i in sf:
        if act.type == parser.NOT:
            polarity = 0 - polarity
        if i == 1:
            if act.type == parser.IMPLIES:
                polarity = 0 - polarity
            act = act.car
        elif i == 2:
            act = act.cdr
        else:
            return None
    if polarity > 0:
        return pynusmv.prop.false()
    else:
        return pynusmv.prop.true()

# Determine if a sub-formula (f1) >= (logically bigger than) another sub-formula (f2)
# In another word, determine if f2 is a sub-formula of f1
    # Example: [1, 2] > [1, 2, 1]
# All the sub-formulas are presented by their positions in the formula
# Position = List containing the trace
# 1 = left
# 2 = right
def bigger(f1, f2):
    if len(f1) > len(f2):
        return False
    else:
        for i in range(len(f1)):
            if (i >= len(f2)) | (f1[i] != f2[i]):
                return False
        return True

# Calculation of minimal sub-formulas of a set of sub-formulas (s)
# All the sub-formulas are presented by their positions in the formula
# So s is a list of lists
def cal_min(s):
    result = []
    for i in range(len(s)):
        is_min = True
        for j in range(i + 1, len(s)):
            if bigger(s[i], s[j]):
                is_min = False
                break
        if is_min == True:
            result.append(copy.copy(s[i]))
    return result

# Return a string emphasizing a given sub-formula (sf) in a formula (spec)
# The sub-formula is represented by its position
def emph_string(sf, spec):
    if str(find_sub_spec(spec, sf)) == 'TRUE':
        temp = replace(spec, sf, pynusmv.prop.false())
    else:
        temp = replace(spec, sf, pynusmv.prop.true())
    s1 = str(temp)
    s2 = str(spec)
    for i in range(len(s1)):
        if s1[i] != s2[i]:
            break
    result = s1[0 : i]
    result += '\033[41;33m'
    result += str(find_sub_spec(spec, sf))
    result += '\033[0m'
    i = i + 4
    if str(find_sub_spec(spec, sf)) == 'TRUE':
        i = i + 1
    result += s1[i :]
    return result