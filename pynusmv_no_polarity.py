import pynusmv
from pynusmv.nusmv.parser import parser
import copy
import pynusmv_formula
import pynusmv_filter

# Class for processing all the sub-formulas without polarity
# In another word : non-polarity processing (npp)
class npp:
    
    def __init__(self, spec):
        # The old spec
        self.original = spec
        
        # We have replaced the sub-formulas without palarity or not
        self.replaced = False

        # The new spec by replacing all the sub-formulas without polarity by formulas with polarity
        self.new = None
        
    # Find out all the IFF sub-formulas (p <-> q) and replace them by (p -> q) & (q -> p)
    # The one after replacement is saved in self.new
    def iff_process(self):
        # Find out the positions of all the IFF sub-formulas
        iff_sf = pynusmv_filter.filter('IFF', self.original)
        iff_sf.sort(key = lambda x:len(x), reverse = True)
        result = copy.copy(self.original)
        # Replace them by formulas with polarity (p -> q) & (q -> p)
        if len(iff_sf) > 0:
            self.replaced = True
            for i in iff_sf:
                # Find out the good position and replace
                p_iff_q = pynusmv_formula.find_sub_spec(result, i)
                p = pynusmv_formula.spec_copy(p_iff_q.car)
                q = pynusmv_formula.spec_copy(p_iff_q.cdr)
                p_implies_q = pynusmv_formula.create_comp(parser.IMPLIES, p, q)
                p = pynusmv_formula.spec_copy(p_iff_q.car)
                q = pynusmv_formula.spec_copy(p_iff_q.cdr)
                q_implies_p = pynusmv_formula.create_comp(parser.IMPLIES, q, p)
                new_one = pynusmv_formula.create_comp(parser.AND, p_implies_q, q_implies_p)
                result = pynusmv_formula.replace(result, i, new_one)
        self.new = result

# Find out all the sub-formulas without polarity and replace them by logically equivalent formulas
# Return a npp object containing all the information
def no_polarity_process(spec):
    result = npp(spec)
    result.iff_process()
    return result