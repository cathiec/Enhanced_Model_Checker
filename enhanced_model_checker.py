import pynusmv
from pynusmv.nusmv.parser import parser
import sys
import copy
import pynusmv_filter
import pynusmv_no_polarity
import pynusmv_formula

# Class containing the result of model-checker for one property (one spec)
# n = -1: no result
# n = -2: set of sub-formulas given is empty
# n =  0: spec is not satisfied
#         l1 is the trace representing the counter example
# n =  1: spec is satisfied but there's vacuity
#         l1 is the list containing the pathes (lists of positions) to each vacuous sub-formula in s
#            so l1 is a list of lists
# n =  2: spec is satisfied and there's no vacuity
#         l1 is the list containing the pathes (lists of positions) to each sub-formula in s
#            so l1 is a list of lists
#         l2 is the list of representing the corresponding interesting witnesses
class model_check_result:
    
    def __init__(self, _n = -1, _npp = None, _l1 = [], _l2 = []):
        self.n = _n
        self.npp = _npp
        self.l1 = copy.copy(_l1)
        self.l2 = copy.copy(_l2)

    def get_formula(self):
        _spec = self.npp.original
        if self.npp.replaced == True:
            _spec = self.npp.new
        return _spec

    def non_satisfied_get_counter_example(self):
        return self.l1
    
    def satisfied_get_vacuous_subformulas_paths(self):
        return self.l1
    
    def satisfied_get_vacuous_subformulas(self):
        vsf = []
        _spec = self.npp.original
        if self.npp.replaced == True:
            _spec = self.npp.new
        for i in self.l1:
            vsf.append(find_sub_spec(_spec, i))
        return vsf
            
    def satisfied_get_all_subformulas_paths(self):
        return self.l1

    def satisfied_get_all_subformulas(self):
        asf = []
        _spec = self.npp.original
        if self.npp.replaced == True:
            _spec = self.npp.new
        for i in self.l1:
            asf.append(find_sub_spec(_spec, i))
        return asf
    
    def satisfied_get_all_interesting_witnesses(self):
        return self.l2

    def show(self):
        print('-------->')
        print('\t', self.npp.original)
        print('-------->')
        if self.n == -1:
            print('Error: No result.')
        elif self.n == -2:
            print('Error: The given set of sub-formulas is empty.\n')
        elif self.n == 0:
            print('Not satisfied. And here is a counter example:')
            for i in self.l1:
                print('\t', i.get_str_values())
        else:
            _spec = self.npp.original
            if self.npp.replaced == True:
                _spec = self.npp.new
                print('   ||\t Sub-formula(s) without polarity has(have) been found.')
                print('   ||\t The formula has been replaced by:')
                print('-------->')
                print('\t', _spec)
                print('-------->')
            if self.n == 1:
                print('Satisfied. And vacuity found:')
                for i in self.l1:
                    emph_str = pynusmv_formula.emph_string(i, _spec)
                    print('\t"', pynusmv_formula.find_sub_spec(_spec, i), '" with path', i,'does not affect ', '"', emph_str, '"', ' in model.')
            elif self.n == 2:
                print('Satisfied. And no vacuity found. Here is(are) an(some) interesting witness(es):')
                ctt = 0
                for i in self.l1:
                    emph_str = pynusmv_formula.emph_string(i, _spec)
                    print('Witness for "', pynusmv_formula.find_sub_spec(_spec, i), '" with path', i, 'in', emph_str, 'is:')
                    for j in self.l2[ctt]:
                        print('\t', j.get_str_values())
                    ctt = ctt + 1

# Find out non-satisfied initial states
def non_satisfied_init_states(spec):
    #print(111)
    nsi_bdd = ~pynusmv.mc.eval_ctl_spec(fsm, spec) & fsm.init
    #print(222)
    nsi_states = fsm.pick_all_states(nsi_bdd)
    return nsi_states

# Enhanced model-checker for one property in SMV model
def check(spec):
    # Determination of satisfaction (Validity of formula)
    nsis = non_satisfied_init_states(spec)
    # If not satisfied, generate a counter-example
    if len(nsis) > 0:
        return model_check_result(0, pynusmv_no_polarity.npp(spec), pynusmv.mc.explain(fsm, min(nsis), spec))
    # If satisfied
    else:
        # Process the sub-formulas without polarity (replace them by formulas with polarity)
        npp = pynusmv_no_polarity.no_polarity_process(spec)
        _spec = npp.new
        # Use the filter to choose the set of sub-formulas (s)
        s = pynusmv_filter.filter(filter_type, _spec)
        # Start tree search in order to find min(S)
        if len(s) == 0:
            return model_check_result(-2, npp)
        min_s = pynusmv_formula.cal_min(s)
        # Vacuity check
        vacuous = False
        list_replaced_spec = []
        list_trace_replaced_spec = []
        list_min_with_witness = []
        list_interesting_witness = []
        for x in min_s:
            # Replacement of sub-formulas
            truth = pynusmv_formula.polarity(_spec, x)
            replaced_spec = pynusmv_formula.find_sub_spec(_spec, x)
            new_spec = pynusmv_formula.replace(_spec, x, truth)
            # Test if new spec is NOT satisfied
            new_bdd = ~pynusmv.mc.eval_ctl_spec(fsm, new_spec) & fsm.init
            new_nsis = fsm.pick_all_states(new_bdd)
            # Find the sub-formula that doesn't affect spec
            if len(new_nsis) == 0:
                list_trace_replaced_spec.append(x)
                list_replaced_spec.append(pynusmv_formula.spec_copy(replaced_spec))
                vacuous = True
            # Generate interesting witnesses if not vacuous
            elif vacuous == False:
                list_min_with_witness.append(x)
                list_interesting_witness.append(pynusmv.mc.explain(fsm, min(new_nsis), new_spec))
        # Return the result
        if vacuous == True:
            return model_check_result(1, npp, list_trace_replaced_spec)
        else:
            return model_check_result(2, npp, list_min_with_witness, list_interesting_witness)
    return model_check_result()

# Enhanced model-checker for all the properties in SMV model
def check_all():
    l = []
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr.cdr
        # We call the enhanced model-checker for one property
        result = check(spec)
        l.append(result)
    return l

################################################################################

# Filename
filename = sys.argv[1]

# Filter type
if len(sys.argv) < 3:
    filter_type = 'all'
else:
    filter_type = sys.argv[2]

print()
print('+>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>')
print('|  SMV Model:')
print('|                ', filename)
print('|  Filter Type:')
print('|                ', filter_type)
print('+<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<')
print()

# Initialization of NuSMV
pynusmv.init.init_nusmv()
print('Initialization sucessed...')

# Load of file
pynusmv.glob.load_from_file(filename)
print('File loaded...')

# Computation of Model
pynusmv.glob.compute_model()
print('Model-computation sucessed...')
fsm = pynusmv.glob.prop_database().master.bddFsm
print('Global properties returned...')

# Use the enhanced model-checker to check all the properties in the SMV model
list_results = check_all()

# Print the results
for r in list_results:
    print()
    r.show()
    print()
    print()
print()

# End of the task
pynusmv.init.deinit_nusmv()