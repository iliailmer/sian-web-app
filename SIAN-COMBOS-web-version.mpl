
###############################################################################
# Part 1: Algorithms for computation with subfields of rational functions
###############################################################################

with(PolynomialIdeals):
#------------------------------------------------------------------------------

IdealsEq := proc(A, B)
    # Checks whether polynomial ideals are equal
    return evalb((A subset B) and (B subset A)):
end:

#------------------------------------------------------------------------------

FieldToIdeal := proc(gens)
    # Input: generators of a subfield of the field of rational functions
    # Computes the MSQ ideal of the field with the new variables of the form x_aux
    # See: https://mediatum.ub.tum.de/doc/685465/document.pdf Definition 2.16
    #      https://doi.org/10.1016/j.jsc.2005.09.010          Lemma 2.1
    local all_vars, subs_dupl, all_dupl, common_denom, polys, f, gb:
    all_vars := indets(gens):
    subs_dupl := map(v -> v = cat(v, _aux), all_vars):
    all_dupl := map(v -> subs(subs_dupl, v), all_vars):
    common_denom := 1:
    polys := []:
    for f in gens do
        common_denom := lcm(common_denom, denom(f)):
        polys := [op(polys), numer(f) * subs(subs_dupl, denom(f)) - subs(subs_dupl, numer(f)) * denom(f)]:
    end do:
    # gb := Groebner[Basis]([op(polys), common_denom * t - 1], plex(t, op(all_dupl))):
    gb := Groebner[Basis]([op(polys), common_denom * t - 1], tdeg(t, op(all_dupl))):
    gb := Groebner[Walk](gb, tdeg(t, op(all_dupl)), lexdeg([t], [op(all_dupl)])):
    gb := select(p -> not (t in indets(p)), gb):
    return PolynomialIdeal(gb, variables=all_dupl):
end proc:

#------------------------------------------------------------------------------

FieldCoefficientRestriction := proc(J, msq_for_subfield)
    # Input: J - a polynomial ideals over a field of rational functions
    #        msq_for_subfield - the MSQ ideal for a subfield E of coefficients (see FieldToIdeal)
    # Computes the radical of the restriction of the ideal to the subfield E 
    # in the sense of https://doi.org/10.1016/j.jsc.2005.09.010 (MSQ-paper in what follows)
    #
    # NOTE: unlike the algorithm in the MSQ-paper, we compute the radical, not the restriction itself
    # one can obtain the algorithm MSQ-paper by replacing PrimeDecomposition with PrimaryDecomposition 
    # in the code below
    local poly_vars, coeff_vars, subs_aux, coeff_aux, gens, subs_aux_msq, gens_msq, msq_ideal_aux, 
    msq_components, J_ext, components, primes_to_keep, P, elim_P, comp, cleaned_ideal:

    poly_vars := IdealInfo[Variables](J):
    coeff_vars := IdealInfo[Parameters](J) union IdealInfo[Parameters](msq_for_subfield):
    subs_aux := map(v -> v = parse(cat(v, _aux_aux)), coeff_vars):
    coeff_aux := subs(subs_aux, coeff_vars):

    # list F of polynomials in the notation of the MSQ-paper, page 375
    gens := map(p -> subs(subs_aux, p * denom(p)), IdealInfo[Generators](J)):

    # Substitution to avoid names clashing between the aux variables in the msq ideal and the variables in J
    subs_aux_msq := map(v -> v = parse(cat(v, _aux)), IdealInfo[Variables](msq_for_subfield)):
    gens_msq := map(p -> subs(subs_aux_msq, p), IdealInfo[Generators](msq_for_subfield)):
    msq_ideal_aux := PolynomialIdeal(gens_msq, variables=map(s -> rhs(s), subs_aux_msq)):
    msq_components := [PrimeDecomposition(msq_ideal_aux)]:

    J_ext := PolynomialIdeal([op(gens), op(gens_msq)], variables=poly_vars union coeff_aux): 
    components := [PrimeDecomposition(J_ext)]:
    
    # Selecting prime components as in Remark on page 377 in MSQ-paper
    primes_to_keep := []:
    for P in components do
        # Going through the prime decomposition of the MSQ-deal mimics the
        # working over the restricted field (which is what has been done in the MSQ-paper)
        elim_P := EliminationIdeal(P, coeff_aux):
        for comp in msq_components do
            if elim_P subset comp then
                primes_to_keep := [op(primes_to_keep), P]:
            end if:
        end do: 
    end do:
    if nops(primes_to_keep) > 0 then
        cleaned_ideal := Intersect(op(primes_to_keep)):
    else
        cleaned_ideal := PolynomialIdeal([0], variables = poly_vars):
    end if:

    # Applying Lemma 2.2 from the MSQ-paper
    return EliminationIdeal(cleaned_ideal, poly_vars):
end proc:

#------------------------------------------------------------------------------


FilterGenerators := proc(ideal)
    # Input: ideal over a rational function field
    # Computes a simplified set of generators of the field of definition
    local gb, gens, p, cf, lc, gsorted, result, big_ideal, cur_ideal, g, new_ideal:
    gb := Groebner[Basis](ideal, tdeg(op(IdealInfo[Variables](ideal)))):
    gens := {}:
    for p in gb do
        cf := sort([coeffs(p, IdealInfo[Variables](ideal))], (a, b) -> length(convert(a, string)) < length(convert(b, string))):
        lc := cf[1]:
        cf := map(c -> c / lc, cf):
        gens := {op(gens), op(cf[2..nops(cf)])}:
    end do:
    gsorted := sort([op(gens)], (a, b) -> length(convert(a, string)) < length(convert(b, string)));
    result := {}:
    big_ideal := FieldToIdeal(gens):
    cur_ideal := FieldToIdeal(result):
    for g in gsorted do
        if big_ideal = cur_ideal then
            return result:
        end if:
        new_ideal := FieldToIdeal({op(result), g}):
        if new_ideal <> cur_ideal then
        	  # a dirty hack to transform -1/a to a
            if convert(g, string)[1] = "-" then
                g := -g:
            end:
            if convert(g, string)[1] = "1" then
                g := 1 / g:
            end:
            result := {op(result), g}:
            cur_ideal := new_ideal:
        end if:
    end do:
    return result:
end proc:

#------------------------------------------------------------------------------

FieldIntersection := proc(gens_left, gens_right)
    # Input: gens_left and gens_right - generators of a subfields E and F of a field of rational functions
    # If terminates, resturns an ideal with field of definition being the intersection of generators of E and F
    # Is guaranteed to terminate if at least one of E and F is algebraically closed in rational functions (see REF)
    # Implementation below is a version of Algorithm 2.38 from https://mediatum.ub.tum.de/doc/685465/document.pdf
    local msq_left, msq_right, poly_vars, coeff_vars, Ii, Ji, gb, result, p, cf, lc;

    msq_left := FieldToIdeal(gens_left):
    msq_right := FieldToIdeal(gens_right):
    poly_vars := IdealInfo[Variables](msq_left) union IdealInfo[Variables](msq_right):
    coeff_vars := IdealInfo[Parameters](msq_left) union IdealInfo[Parameters](msq_right):

    Ii := PolynomialIdeal([1], variables=poly_vars):
    Ji := msq_left:

    while not IdealsEq(Ii, Ji) do
        Ii := FieldCoefficientRestriction(Ji, msq_right):
        Ji := FieldCoefficientRestriction(Ii, msq_left):
    end do:

    return Ji:
end proc:

#------------------------------------------------------------------------------

CompareFields := proc(gens_l, gens_r)
    # Checks whether gens_l and gens_r generate the same subfield of rational functions
    return IdealsEq(FieldToIdeal(gens_l), FieldToIdeal(gens_r)):
end proc:


#------------------------------------------------------------------------------

###############################################################################
# Part 2: Algorithm for computing  identifiable functions
###############################################################################

with(DifferentialAlgebra):

#===============================================================================

ExtractDenominator := proc(model)
    # Input: model a list of rational functions
    # returns the function multiplied by their denominators and 
    # an inequality corresponding to the LCM of the denominators
    local common_denom, r;
    common_denom := 1:
    for r in model do
        common_denom := lcm(common_denom, denom(r)):
    end do:
    return [op(map(p -> denom(p) * p, model)), common_denom <> 0]:
end proc:

#===============================================================================
CheckReducibilitySet := proc(polys, charset)
    # Input: polys - list of differential polynomials
    #        charset - a characteristic set
    # Returns true iff all the polynomials are reduced to zero wrt to the charset
    local result, e:
    result := true:
    for e in polys do
        if NormalForm(e, charset) <> 0 then
            result := false:
            break:
        end if:
    end do:
    return result:
end proc:
#===============================================================================

GetIOEquations := proc(model, states, inputs, outputs, params, use_brackets, infolevel, target)
    # Input: model - list of differential polynomials defining the model
    #        states, ios, params - list of names of state variables, input-output variables
    #                              and parameter, respectively
    # Computes a list of input-output equations of the model
    local Relim, Rorig, charsets, chset_orig, general_comps, general, c, e, gen_comp, io_eqs:
    Relim := DifferentialRing(blocks = [[op(states)], [op(outputs)], [op(inputs)]], derivations = [t], arbitrary = params):
    if not use_brackets then
        Relim := DifferentialRing(blocks = [[op(states)], op(outputs), [op(inputs)]], derivations = [t], arbitrary = params):
    end if:
    Rorig := DifferentialRing(blocks = [[op(outputs)], [op(states)], [op(inputs)]], derivations = [t], arbitrary = params):
           # DifferentialRing(blocks = [[op(inputs)], [op(outputs)], [op(states)]], derivations = [t], arbitrary = params):
    chset_orig := RosenfeldGroebner(model, Rorig)[1]:
    
 
    if infolevel > 0 then
        LogText(sprintf("    Computing the characteristic set (singsol = none)\n"), target):
    end if:
    charsets := RosenfeldGroebner(model, Relim, singsol = none):
    if CheckReducibilitySet(Equations(charsets[1]), chset_orig) then        
        gen_comp := charsets[1]:
    else
        if infolevel > 0 then
            LogText(sprintf("    Did not pick the right component. Using singsol = all\n"), target):
        end if:
        charsets := RosenfeldGroebner(model, Relim):
        if infolevel > 0 then
            LogText(sprint("    Selecting the general component\n"), target):
        end if:
        general_comps := []:
        for c in charsets do
            general := true:
            for e in Equations(c) do
                if NormalForm(e, chset_orig) <> 0 then
                    general := false:
                    break:
                end if:
            end do:
            if general then
                general_comps := [op(general_comps), c]:
            end if:
        end do:
        if nops(general_comps) > 1 then
            LogText(sprintf("More than one component is considered general!", general_comps), target):
        end if:
        gen_comp := general_comps[1]:
    end if:
    io_eqs := Equations(gen_comp, leader < parse(cat(states[-1], "(t)"))):
    return io_eqs:
end proc:

#===============================================================================

# Adapted from 
# https://www.mapleprimes.com/questions/36772-Extract-Specific-Coefficients-Of-A-Multivariate
# by Kitonum 15364
coefff:=proc(P, t)
    local L, H, i, k:
    L:=[coeffs(P, indets(P), 'h')]: H:=[h]: k:=0:
    for i from 1 to nops(H) do
        if H[i]=t then k:=L[i] fi:
    end do:
    return k;
end proc:

#===============================================================================

DecomposePolynomial := proc(p, vars_main, vars_coef, infolevel, target)
    # Input: p - polynomial in two groups of variables: vars_main and vars_coef
    # Computes a decomposition of minimal length of p as a linear combination 
    # of products A * B, where A is a polynomial in vars_main and B 
    # is a polynomial in vars_coef return two lists: list of A's and list of B's
    local cf, monoms, result_cf, result_monom, i, c, m, j, lc, lm, coeff_in_c:
    cf := [coeffs(collect(p, vars_main, 'distributed'), vars_main, 'monoms')]:
    monoms := [monoms]:
    result_cf := []:
    result_monom := Array([]):
    if infolevel > 0 then
        LogText(sprintf("        Number of monomials: %a\n", nops(cf)), target):
    end:
    for i from 1 to nops(cf) do
        c := cf[i]:
        m := monoms[i]:
        for j from 1 to nops(result_cf) do
            lc, lm := Groebner[LeadingTerm](result_cf[j], plex(op(vars_coef))):
            coeff_in_c := coefff(c, lm):
            c := c - coeff_in_c / lc * result_cf[j]:
            result_monom[j] := result_monom[j] + coeff_in_c / lc * m:
        end do:
        if c <> 0 then
            result_cf := [op(result_cf), c]:
            ArrayTools[Append](result_monom, m):
        end if:
    end do:
    if infolevel > 0 then
        LogText(sprintf("        Reduced to: %a\n", nops(result_cf)), target):
    end:
    return [result_cf, convert(result_monom, list)]:
end proc:

#===============================================================================

ConstructWronskian := proc(io_eq, model, states, inputs, outputs, params, state_space, infolevel, target)
    # Input - the same as for GetIOEquations + one IO-equation + flag subs_param
    # Computes the Wronskian for this equation using the representation
    # given by DecomposePolynomial. Return a pair of the Wronskian
    # reduced modulo the original system and a list of coefficients
    # of the compressed io_eq
    local getNormalForm, diff_to_ord, v, vt, h, v_ord, vd, p, decomp, diff_polys, Rorig, chset_orig,
    M, yus, yus_reduced, yus_list, M_sub, roll, params_sub, ios, ps_sol, ps, i:

    diff_to_ord := {}:
    ios := [op(inputs), op(outputs)]:
    for v in ios do
        vt := parse(cat(v, "(t)")):
        diff_to_ord := {op(diff_to_ord), vt = v}:
        for h from 1 to nops(states) + 1 do
            v_ord := parse(cat(v, "_", h)):
            vd := diff(vt, t$h):
            diff_to_ord := {op(diff_to_ord), vd = v_ord}:
        end do:
    end do:
    p := subs(diff_to_ord, io_eq):
    if infolevel > 0 then
        LogText(sprintf("    Combining monomials to reduce the dimension\n"), target):
    end if:
    decomp := DecomposePolynomial(p, map(e -> rhs(e), diff_to_ord), params, infolevel, target):
    diff_polys := map(p -> subs(map(e -> rhs(e) = lhs(e), diff_to_ord), p), decomp[2]):
    Rorig := DifferentialRing(blocks = [[op(outputs)], [op(states)], [op(inputs)]], derivations = [t], arbitrary = params):
           # DifferentialRing(blocks = [[op(inputs)], [op(outputs)], [op(states)]], derivations = [t], arbitrary = params):
    chset_orig := RosenfeldGroebner(model, Rorig)[1]:
    
    if infolevel > 0 then
        LogText(sprintf("    Computing the Wronskian\n"), target):
    end if:
    M := VectorCalculus[Wronskian](diff_polys, t):
    yus := indets(M) minus {t}:

    if infolevel > 0 then
        LogText(sprintf("    Reducing the Wronskian\n"), target):
    end if:
    if state_space <> [] then
        ps_sol := GetPSSolution(state_space, nops(yus)):
        yus_reduced := []:
        for v in ios do
            vt := parse(cat(v, "(t)")):
            ps := subs(ps_sol, v(t)):
            for i from 0 to nops(yus) - 1 do
                yus_reduced := [op(yus_reduced), vt = subs({t = 0}, ps)]:
                vt := diff(vt, t):
                ps := diff(ps, t):
            end do:
        end do:
    else
        getNormalForm := proc (p, chset_orig)
            return p=DifferentialAlgebra:-NormalForm(p, chset_orig):
        end proc:
        Rorig := DifferentialRing(blocks = [[op(outputs)], [op(states)], [op(inputs)]], derivations = [t], arbitrary = params):
               # DifferentialRing(blocks = [[op(inputs)], [op(outputs)], [op(states)]], derivations = [t], arbitrary = params):
        chset_orig := RosenfeldGroebner(model, Rorig)[1]:
        yus_list := convert(yus, list):
        yus_reduced:=Threads:-Seq[tasksize=nops(yus_list)](getNormalForm(yus_list[i], chset_orig), i =1..nops(yus_list)):
        # yus_reduced := map(p -> p = NormalForm(p, chset_orig), yus):
    end if:
    
    # iofun:=map(y->parse(cat(convert(y, string), "(t)")), ios):
    # derivative_orders:=table([seq(p=0, p in iofun)]):
    # for each in yus_list do
    #     indets_ := indets(each) minus {t}: # get indets of derivative to compute order
    #     function_ := op(indets_ intersect {op(iofun)}): # for which function?
    #     order:=numelems(indets_): # compute order
    #     if derivative_orders[function_]<order then
    #         derivative_orders[function_]:=order;
    #     fi:
    # end do;
    # LogExpression(derivative_orders):
    # yus_reduced:=[]:
    # count:=0:
    # # yus_reduced:=Threads:-Seq[tasksize=nops(yus_list)](getNormalForm(yus_list[i], chset_orig), i =1..nops(yus_list)):
    # for y in ios do
    #     y:=parse(cat(convert(y, string), "(t)")):
    #     y_rem:=y:
    #     fun:=y:
    #     while count<derivative_orders[fun] do
    #         yus_reduced:=[op(yus_reduced), y=DifferentialAlgebra:-NormalForm(y_rem, chset_orig)]:
    #         count := count+1:
    #         y_rem:=diff(y_rem, t):
    #         y:=diff(y, t):
    #         LogText("Done Processing %a, order: %a\n", fun, count):
    #     end do:
    #     count:=0:
    # end do:

    
    M_sub := subs(yus_reduced, M):
    M_sub := subs(map(x -> parse(cat(x, "(t)")) = x, states), M_sub):
    return [M_sub, decomp[1]]:
end proc:

#===============================================================================

SingleExperimentIdentifiableFunctions := proc(model, output_targets, {infolevel := 1})
    # Input: model - ODE model represented as a list of differential polynomials
    # Computes generators of the field of single-identifiable functions
    local result, start, finish, states, inputs, outputs, model_eq, ios, params, io_eqs, si_gens, eq, wrnsk, echelon_form, model_denomfree, target: 	
    states, inputs, outputs, params, model_eq := op(ParseInput_(model)): # states, ios, params := op(ParseInput_(model)):
    ios := [op(inputs), op(outputs)]:

    # Step 1
    if infolevel > 0 then
        LogText(sprintf("SE Step 1: Computing input-output equations\n"), output_targets[log]):
    end if:
    model_denomfree := ExtractDenominator(model_eq):
    io_eqs := GetIOEquations(model_denomfree, states, inputs, outputs, params, false, infolevel, output_targets[log]):
    if infolevel > 0 then
        LogText(sprintf("SE Total number of io-equations: %a\n", nops(io_eqs)), output_targets[log]):
    end if:

    	    si_gens := {}:
	    for eq in io_eqs do
	        # Step 2
	        if infolevel > 0 then
	            LogText(sprintf("SE Step 2: Constructing the Wronskian\n"), output_targets[log]):
	        end if:
	        wrnsk := ConstructWronskian(eq, model_denomfree, states, inputs, outputs, params, [], infolevel, output_targets[log])[1]:
	        # Step 3
	        if infolevel > 0 then
	            LogText(sprintf("SE Step 3: Computing the reduced row echelon form of the Wronskian\n"), output_targets[log]):
	        end if:
	        echelon_form := LinearAlgebra[ReducedRowEchelonForm](wrnsk):
	        si_gens := {op(si_gens), op(select(x -> not type(x, numeric), convert(echelon_form, list)))}:
	    end do:

    # Step 4
    if infolevel > 0 then
        LogText(sprintf("SE Step 4: restricting to the field of parameters"), output_targets[log]):
    end if:
    	result:=map(simplify, convert(FilterGenerators(FieldIntersection(si_gens, params)), list)):
	DocumentTools:-SetProperty(output_targets[single], expression, result, 'refresh'):
	return result:
end proc:

#===============================================================================
# Adapted from https://github.com/pogudingleb/SIAN
FunctionToVariable_ := proc(f):
    convert(convert(f, string)[1..-4], symbol):
end proc:

ParseInput_ := proc(model)
   local all_symbols, x_functions, io_functions, params, states, ios, diff_polys, lhss, out_functions, in_functions, inputs, outputs:
   diff_polys := map(eq -> lhs(eq) - rhs(eq), model):
   all_symbols := foldl(`union`, op( map(e -> indets(e), diff_polys) )) minus {t}:
   x_functions := map(f -> int(f, t), select( f -> type(int(f, t), function(name)), all_symbols )):
   io_functions := select( f -> not type(int(f, t), function(name)) and type(f, function(name)) and not f in x_functions, all_symbols ):
   lhss := map(eq -> lhs(eq), model):
   out_functions := select(f -> f in lhss, io_functions):
   in_functions := select(f -> not (f in lhss), io_functions):
   params := [op(select(f -> not type(f, function(name)) and not type(int(f, t), function(name)), all_symbols))]:
   states := [op(map(FunctionToVariable_, x_functions))]:
   inputs := [op(map(FunctionToVariable_, in_functions))]:
   outputs := [op(map(FunctionToVariable_, out_functions))]:
   return [states, inputs, outputs, params, diff_polys]:
end proc:

#===============================================================================

MultiExperimentIdentifiableFunctions := proc(model, simplified_generators, no_bound, simplify_bound, max_perms, output_targets): # {simplified_generators := false, no_bound := false})
    # Input: model - ODE model in the state-space form
    # Computes the bound from Theorem REF. Returns a list containing
    # 1. the bound
    # 2. the list of lists of coefficients of the IO-equations (after compression)
    # 3. (optional) simplified set of generators of the field of multi-experiment identifiable functions
    #
    # Optional keyword arguments:
    # 1. simplified_generators - if False, then just the coefficients of the IO-equations are returned.
    #                            if True, they are being simplified (maybe be a substantial simplification)
    #                            but this takes time
    # 2. no_bound - if True, then bound for the number of experiments is not computed (may save a lot of time)

    local states, inputs, outputs, ios, params, model_eqs, io_eqs, io_coeffs, io_coef, wrnsk, s, roll, wrnsk_sub, r, bound, 
    generators, i, eq, result, model_denomfree, target, start, finish, infolevel, use_brackets, output_permutations, 
    outputs_, io_coeffs_sb, io_eqs_sb, bound_sb, skip_simplify, result_sb, best_output_ordering, returned_generators, idx, old_bound:

    states, inputs, outputs, params, model_eqs := op(ParseInput_(model)):
    use_brackets:=false:
    output_permutations := combinat[permute](outputs):
    output_permutations:= output_permutations[..min(nops(output_permutations),max_perms)];
    
    infolevel := 1:
    model_denomfree := ExtractDenominator(model_eqs):
    skip_simplify := false:
    old_bound := 10: # this will be replaced by a smaller boud every time
    idx:=0:
    for use_brackets in [true, false] do
        for outputs in output_permutations do
        	LogText(sprintf("Permutation:\t%a\n", outputs),  output_targets[log]):
        	# the first iteration is default permutation
	    	   LogText(sprintf("Use Brackets?\t%a\n", use_brackets), output_targets[log]):
	        if infolevel > 0 then
	            LogText(sprintf("ME Computing input-output equations\n"), output_targets[log]):
	   	   end if:
	   	   io_eqs := GetIOEquations(model_denomfree, states, inputs, outputs, params, use_brackets, infolevel, output_targets[log]):
	   	   if infolevel > 0 then
	            LogText(sprintf("ME Total number of io-equations: %a\n", nops(io_eqs)), output_targets[log]):
	        end if:
	        io_coeffs := []:
	        
	        for eq in io_eqs do
	            io_coef := DecomposePolynomial(eq, indets(eq) minus {op(params)}, params, infolevel, output_targets[log])[1]:
	            io_coeffs := [op(io_coeffs), io_coef]:
	        end do:

	        generators := {}:
    	        for io_coef in io_coeffs do
                 io_coef := sort(io_coef, (a, b) -> length(convert(a, string)) < length(convert(b, string)));
                 for i from 2 to nops(io_coef) do
                     generators := {op(generators), io_coef[i] / io_coef[1]}:
                 end do:
              end do:
              bound := 0:
		    if no_bound = false then
                  for eq in io_eqs do
                      if infolevel > 0 then
                          LogText(sprintf("ME Constructing the Wronskian\n"), output_targets[log]):
                      end if:
                      wrnsk, io_coef := op(ConstructWronskian(eq, model_denomfree, states, inputs, outputs, params, model, infolevel, output_targets[log])):
                      # in the notation of the theorem
                      s := nops(io_coef) - 1:
                      # substitution does not increase the rank, so the resulting bound will be correct
                      roll := rand(1..15):
                      wrnsk_sub := map(v -> v = roll(), indets(wrnsk)):
                      r := LinearAlgebra[Rank](subs(wrnsk_sub, wrnsk)):
                      bound := max(bound, s - r + 1):
                  end do:
               end if:
               if bound<old_bound or idx=0 then # idx makes sure we assign a new bound at the first run
               	old_bound:=bound:
               end if:
               idx := idx +1;
               LogText(sprintf("New Bound:\t%a\n", bound),  output_targets[log]):
               result := [old_bound, generators]:
               if simplified_generators then
                   if infolevel > 0 then
		             LogText(sprintf("ME WARNING: Entering simplification of generators! if this takes too long, try unchecking \"Simplified Generators\"\n"), output_targets[log]):
                   end if:
                   result := [op(result), FilterGenerators(FieldToIdeal(generators))]:
                   DocumentTools:-SetProperty(output_targets[multi], expression, map(simplify, convert(result[3], list)), 'refresh'):
                   returned_generators := result[3]:
               else
                   DocumentTools:-SetProperty(output_targets[multi], expression, map(simplify, convert(result[2], list)), 'refresh'):
                   returned_generators := result[2]:
               end if:
               if old_bound > 0 then
    	              DocumentTools:-SetProperty(output_targets[bound_], expression, old_bound, 'refresh'):
    	              if old_bound=1 then
    	  	             skip_simplify := true:
    	  	             if simplify_bound then
    	  		            LogText(sprintf("Bound on the number of experiments = 1, \"Try to refine bound\" was selected but it will be skipped"), output_targets[log]):
    	  	             end if:
	        	        if simplified_generators then
       		            DocumentTools:-SetProperty(output_targets[single], expression, map(simplify, convert(result[3], list)), 'refresh'):
   		             else
    	   		            DocumentTools:-SetProperty(output_targets[single], expression, map(simplify, convert(result[2], list)), 'refresh'):
   		             end if:
    	              end if:
               else
	              DocumentTools:-SetProperty(output_targets[bound_], expression, "",'refresh'):
               end if:
               if skip_simplify or not simplify_bound then
               	break:
              	else
              		DocumentTools:-SetProperty("being_refined", caption, "being refined", 'refresh'):
               end if:
         end do: # loop over outputs
         if skip_simplify or not simplify_bound then
             # only breaks if we do not simplify. the code runs at most once
             break:
         end if:
    end do:
    DocumentTools:-SetProperty("being_refined", caption, "", 'refresh'):
    return [bound, returned_generators];#table([bd=bound]):
end proc:

GetPSSolution := proc(model, ord)
    # Input: model and integer ord
    # Output: a truncated power series solution with random parameter values
    # and initial conditions of order ord
    local roll, states, inputs, outputs, params, model_eqs, model_sub,
    x_funcs, x_sols, x_eqs, cur_ord, i, rhs_eval, total_sub, y_funcs, y_sols,
    params_subs, input_subs:
    roll := rand(1..15):
    states, inputs, outputs, params, model_eqs := op(ParseInput_(model)):
    params_subs := map(p -> p = roll(), params):
    input_subs := map(u -> parse(cat(u, "(t)")) = add([seq(roll() * t^i, i=0..ord)]), inputs):
    model_sub := subs(params_subs, model):
    model_sub := subs(input_subs, model_sub):
    x_funcs := map(x -> parse(cat(x, "(t)")), states):
    x_sols := map(x -> x = roll(), x_funcs):
    x_eqs := map(x -> subs(model_sub, diff(x, t)), x_funcs):
    
    for cur_ord from 1 to ord do
        for i from 1 to nops(x_funcs) do
            rhs_eval := series(subs(x_sols, x_eqs[i]), t, ord + 1):
            x_sols[i] := (lhs(x_sols[i]) = (rhs(x_sols[i]) + t^cur_ord * coeff(rhs_eval, t, cur_ord - 1) / cur_ord)):
        end do:
    end do:
  
    total_sub := [op(x_sols), op(params_subs), op(input_subs)]:
    y_funcs := map(y -> parse(cat(y, "(t)")), outputs):
    y_sols := map(y -> y = subs(total_sub, subs(model_sub, y)), y_funcs):
  
    return [op(y_sols), op(input_subs), op(params_subs), op(x_sols)]:
end proc:

#===============================================================================

#===============================================================================
IdentifiabilityODE := proc(system_ODEs, params_to_assess, p, output_targets, count_solutions, char)#{p := 0.99, infolevel := 1, method := 2, num_nodes := 6}) 
#===============================================================================
 local i, j, k, n, m, s, all_params, all_vars, eqs, Q, X, Y, poly, d0, D1, 
        sample, all_subs,alpha, beta, Et, x_theta_vars, prolongation_possible, 
        eqs_i, JacX, vars, vars_to_add, ord_var, var_index, deg_variety, D2, 
        y_hat, u_hat, theta_hat, Et_hat, Q_hat, theta_l, theta_g, gb, v, X_eq, Y_eq, 
        poly_d, separant, leader, x_functions, y_functions, u_functions,
        all_symbols_rhs, mu, x_vars, y_vars, u_vars, theta, subst_first_order,
        subst_zero_order, x_eqs, y_eqs, param, other_params, to_add, at_node,
        prime, max_rank, R, tr, e, p_local, xy_ders, polys_to_process, new_to_process, method, start, finish, infolevel,
        num_nodes ,Et_x_vars, out_sian, var, G, P, solutions_table, check:

  #----------------------------------------------
  # 0. Extract inputs, outputs, states, and parameters from the system
  #----------------------------------------------
  method := 2:
  
  if SearchText(".", convert(system_ODEs, string)) <> 0 then
    LogText(sprintf("WARNING: It looks like your system involves floating-point numbers. This may result into a non-meaninful result, please convert them to rationals (e.g., 0.2 -> 1/5)"), "LogAreaSIAN"):
    WARNING("WARNING: It looks like your system involves floating-point numbers. This may result into a non-meaninful result, please convert them to rationals (e.g., 0.2 -> 1/5)"):
  end if:
  
  if not (indets(system_ODEs, name) subset indets(system_ODEs)) then
    LogText(sprintf(cat("ERROR: you are using reserved maple symbols: ", convert(indets(system_ODEs, name) minus indets(system_ODEs), string))), output_targets[log]):
    DocumentTools:-SetProperty("GlobalParams1", expression, Error(BadName)):
    DocumentTools:-SetProperty("LocalParams1", expression,  Error(BadName)):
    DocumentTools:-SetProperty("NoIDParams1", expression,  Error(BadName)):
    error (cat("ERROR: you are using reserved maple symbols: ", convert(indets(system_ODEs, name) minus indets(system_ODEs), string))):
    return;
  end if:
  
  randomize():
  infolevel:=1:
  num_nodes:=1:
  if infolevel > 0 then
    PrintHeader("0. Extracting states, inputs, outputs, and parameters from the system"):
  end if:
  x_functions := map(f -> int(f, t), select( f -> type(int(f, t), function(name)), map(lhs, system_ODEs) )):
  y_functions := select( f -> not type(int(f, t), function(name)), map(lhs, system_ODEs) ):
  all_symbols_rhs := foldl(`union`, op( map(e -> indets(rhs(e)), system_ODEs) )) minus {t}:
  xy_ders := {op(x_functions), op(y_functions), op(select(f -> (f in all_symbols_rhs), map(lhs, system_ODEs)))}:
  u_functions := select( f -> type(f, function), convert(all_symbols_rhs minus xy_ders, list)):
  mu := convert(all_symbols_rhs minus {op(xy_ders), op(u_functions)}, list):

  x_vars := map(FunctionToVariable, x_functions):
  y_vars := map(FunctionToVariable, y_functions):
  u_vars := map(FunctionToVariable, u_functions):
  theta := map(ParamToInner, params_to_assess):
  subst_first_order := {seq(diff(x_functions[i], t) = MakeDerivative(x_vars[i], 1), i = 1 .. nops(x_vars))}:
  subst_zero_order := {
    seq(x_functions[i] = MakeDerivative(x_vars[i], 0), i = 1 .. nops(x_vars)),
    seq(y_functions[i] = MakeDerivative(y_vars[i], 0), i = 1 .. nops(y_vars)),
    seq(u_functions[i] = MakeDerivative(u_vars[i], 0), i = 1 .. nops(u_vars))
  }:
  x_eqs := subs(subst_zero_order, subs(subst_first_order, select(e -> type(int(lhs(e), t), function(name)), system_ODEs))):
  y_eqs := subs(subst_zero_order, select(e -> not type(int(lhs(e), t), function(name)), system_ODEs)):

  # taking into account that fact that Groebner[Basis] is Monte Carlo with probability of error 
  # at most 10^(-18) (for Maple 2017)
  p_local := p + nops(params_to_assess) * 10^(-18):
  if p_local >= 1 then
    LogTextSIAN("The probability of success cannot exceed 1 - #params_to_assess 10^{-18}. We reset it to 0.99");
    p_local := 0.99:
  end if:

  if infolevel > 0 then
    LogText(sprintf("\n===== Input info =====\n"), output_targets[log]): 
    LogText(sprintf("%s %a\n", `State variables:         `, x_functions), output_targets[log]): 
    LogText(sprintf("%s %a\n", `Output variables:        `, y_functions), output_targets[log]): 
    LogText(sprintf("%s %a\n", `Input variables:         `, u_functions), output_targets[log]): 
    LogText(sprintf("%s %a\n", `Parameters in equations: `, mu), output_targets[log]): 
    LogText(sprintf("===================\n\n"), output_targets[log]): 
  end if:

  #----------------------------------------------
  # 1. Construct the maximal system.
  #----------------------------------------------

  if infolevel > 0 then
    PrintHeader("1. Constructing the maximal polynomial system"):
  end if:

  # (a) ---------------
  n := nops(x_vars):
  m := nops(y_vars):
  s := nops(mu) + n:
  all_params := [op(mu), op(map(x -> MakeDerivative(x, 0), x_vars ))]:
  all_vars := [ op(x_vars), op(y_vars), op(u_vars) ]:
  eqs := [op(x_eqs), op(y_eqs)]:
  Q := foldl( (f, g) -> lcm(f, g), op( map(f -> denom(rhs(f)), eqs) )):
  

  # (b,c) ---------------
  X := []:
  X_eq := []:
  for i from 1 to n do
    X := [op(X), []]:
    poly := numer(lhs(x_eqs[i]) - rhs(x_eqs[i])):
    for j from 0 to s + 1 do
      poly_d := Differentiate(poly, all_vars, j):
      leader := MakeDerivative(x_vars[i], j + 1):
      separant := diff(poly_d, leader):
      X[i] := [op(X[i]), poly_d]:
      X_eq := [op(X_eq), leader = -(poly_d - separant * leader) / separant]:
    end do:
  end do:
  # LogExpression(X[1]);
  
  # (d,e) ---------------
  Y := []:
  Y_eq := []:
  for i from 1 to m do
    Y := [op(Y), []]:
    poly := numer(lhs(y_eqs[i]) - rhs(y_eqs[i])):
    for j from 0 to s + 1 do
      poly_d := Differentiate(poly, all_vars, j):
      leader := MakeDerivative(y_vars[i], j):
      separant := diff(poly_d, leader):
      Y[i] := [op(Y[i]), poly_d]:
      Y_eq := [op(Y_eq), leader = -(poly_d - separant * leader) / separant]:
    end do:
  end do:


  #----------------------------------------------
  # 2. Truncate.
  #----------------------------------------------

  if infolevel > 0 then
    PrintHeader("2. Truncating the polynomial system based on the Jacobian condition"):
  end if:

  # (a) ---------------
  d0 := max(op( map(f -> degree( simplify(Q * rhs(f)) ), eqs) ), degree(Q)):

  # (b) ---------------
  # extra factor nops(theta) + 1 compared to the formula in the paper is to
  # provide probability gaurantee to the local identifiability test
  D1 := floor( (nops(theta) + 1) * 2 * d0 * s * (n + 1) * (1 + 2 * d0 * s) / (1 - p_local) ):
  # prime := nextprime(D1):
  if infolevel > 1 then
    LogText(sprintf("%s %a\n", `Bound D_1 for testing the rank of the Jacobian probabilistically: `, D1), output_targets[log]);
  end if:

  # (c, d) ---------------
  sample := SamplePoint(D1, x_vars, y_vars, u_vars, mu, X_eq, Y_eq, Q):
  all_subs := sample[4]:
  u_hat := sample[2]:
  y_hat := sample[1]:
 
  # (e) ------------------
  alpha := [seq(1, i = 1..n)]:
  beta := [seq(0, i = 1..m)]:
  Et := [];
  # TODO: improve for arbitrary derivatives
  x_theta_vars := all_params:
  prolongation_possible := [seq(1, i = 1..m)]:

  # (f) ------------------
  while add(prolongation_possible) > 0 do
    for i from 1 to m do
      if prolongation_possible[i] = 1 then
        eqs_i := [op(Et), Y[i][beta[i] + 1]]:
        JacX := VectorCalculus[Jacobian](subs({op(u_hat), op(y_hat)}, eqs_i), x_theta_vars = subs(all_subs, x_theta_vars)):
        if LinearAlgebra[Rank](JacX) = nops(eqs_i) then
          Et := [op(Et), Y[i][beta[i] + 1]]:
          beta[i] := beta[i] + 1:
          # adding necessary X-equations
          polys_to_process := [op(Et), seq(Y[k][beta[k] + 1], k=1..m)]:
          while nops(polys_to_process) <> 0 do
            new_to_process := []:
            vars := {};
            for poly in polys_to_process do
              vars := vars union { op(GetVars(poly, x_vars)) }:
            end do:
            vars_to_add := { op(remove(v -> evalb(v in x_theta_vars), vars)) };
            for v in vars_to_add do
              x_theta_vars := [op(x_theta_vars), v];
              ord_var := GetOrderVar(v);
              var_index := ListTools[Search](ord_var[1], x_vars):
              poly := X[ var_index ][ ord_var[2] ]:
              Et := [op(Et), poly]:
              new_to_process := [op(new_to_process), poly]:
              alpha[ var_index ] := max(alpha[ var_index ], ord_var[2] + 1):
            end do:
            polys_to_process := new_to_process:
          end do:
        else
          prolongation_possible[i] := 0;
        end if:
      end if: 
    end do:
  end do:
  # is used for assessing local identifiabilty
  max_rank := nops(Et):

  # (g) --------------
  for i from 1 to m do
    for j from beta[i] + 1 to nops(Y[i]) do
      to_add := true:
      for v in GetVars(Y[i][j], x_vars) do
        if not (v in x_theta_vars) then
          to_add := false:
        end if:
      end do:
      if to_add = true then
        beta[i] := beta[i] + 1:
        Et := [op(Et), Y[i][j]]:
      end if:
    end do:
  end do:
 
  if infolevel > 1 then
    LogText(sprintf("%s %a\n", `Orders of prolongations of the outputs (beta) = `, beta), output_targets[log]):
    LogText(sprintf("%s %a\n", `Orders of prolongations of the state variables (alpha) = `, alpha), output_targets[log]):
  end if:
  ##############################

  if infolevel > 0 then
    PrintHeader("3. Assessing local identifiability"):
  end if:
 
  theta_l := []:
  for param in theta do
    other_params := subs(param = NULL, x_theta_vars):
    JacX := VectorCalculus[Jacobian]( 
        subs( { op(u_hat), param = subs(all_subs, param), op(y_hat) }, Et), 
        other_params = subs(all_subs, other_params)
    ):
    if LinearAlgebra[Rank](JacX) <> max_rank then
      theta_l := [op(theta_l), param]:
    end if:
  end do:
 
  if infolevel > 1 then
    LogText(sprintf("%s %a\n", `Locally identifiable paramters: `, map(x -> ParamToOuter(x, all_vars), theta_l)), output_targets[log]);
    LogText(sprintf("%s %a\n", `Nonidentifiable parameter: `, map(x -> ParamToOuter(x, all_vars), [op({op(theta)} minus {op(theta_l)})])), output_targets[log]);
  end if:

  DocumentTools:-SetProperty(output_targets[localparams], expression, map(x -> ParamToOuter(x, all_vars), theta_l), 'refresh'): # local
  DocumentTools:-SetProperty(output_targets[noidparams], expression, map(x -> ParamToOuter(x, all_vars), [op({op(theta)} minus {op(theta_l)})]), 'refresh'): # no id

  #----------------------------------------------
  # 3. Randomize.
  #----------------------------------------------

  if infolevel > 0 then
    PrintHeader("4. Randomizing the truncated system"):
  end if:

  # (a) ------------
  deg_variety := foldl(`*`, op( map(e -> degree(e), Et) )):
  D2 := floor( 6 * nops(theta_l) * deg_variety * (1 + 2 * d0 * max(op(beta))) / (1 - p_local) ):
  if infolevel > 1 then
    LogText(sprintf("%s %a\n", `Bound D_2 for assessing global identifiability: `, D2), output_targets[log]):
  end if:

  # (b, c) ---------
  sample := SamplePoint(D2, x_vars, y_vars, u_vars, mu, X_eq, Y_eq, Q):
  y_hat := sample[1]:
  u_hat := sample[2]:
  theta_hat := sample[3]:
  if infolevel > 1 then
    LogText(sprintf("%s %a\n", `Random sample for the outputs and inputs is generated from `, theta_hat), output_targets[log]):
  end if:

  # (d) ------------
  Et_hat := map(e -> subs([op(y_hat), op(u_hat)], e), Et):
  Et_x_vars := {}:
  for poly in Et_hat do
    Et_x_vars := Et_x_vars union { op(GetVars(poly, x_vars)) }:
  end do:
  if infolevel > 1 then
 #   LogText("%s %a %s %a %s\n", `The polynomial system \widehat{E^t} contains `, nops(Et_hat), `equations in `, nops(Et_x_vars) + nops(mu), ` variables`);
 # end if:
  Q_hat := subs(u_hat, Q):

  vars := [
    op(sort([op(Et_x_vars)], (a, b) -> CompareDiffVar(a, b, x_vars))),
    z_aux, w_aux,
    op(sort(mu))
  ]:
  if infolevel > 1 then
    LogText(sprintf("Variable ordering to be used for Groebner basis computation %a\n", vars), output_targets[log]);
  end if:
 
  #----------------------------------------------
  # 4. Determine.
  #----------------------------------------------

  if infolevel > 0 then
    PrintHeader("5. Assessing global identifiability"):
  end if:

  theta_g := []:
  if method = 1 then
    at_node := proc(var, args_node)
      local gb_loc, fname;
      gb_loc := Groebner[Basis](op(args_node)):
      gb_loc;
    end proc:

    if nops(theta_l) > 1 and num_nodes > 1 then
      Grid[Setup]("local", numnodes = num_nodes):
      Grid[Set](at_node):
      gb := Grid[Seq](
        at_node(theta_l[i], [
          [op(Et_hat), z_aux * Q_hat - 1, (theta_l[i] - subs(theta_hat, theta_l[i])) * w_aux - 1],
          tdeg(vars)
        ]),
        i = 1..nops(theta_l)
      ):
    else
      gb := []:
      for i from 1 to nops(theta_l) do
        gb := [
          op(gb), 
          at_node(
            theta_l[i], 
            [[op(Et_hat), z_aux * Q_hat - 1, (theta_l[i] - subs(theta_hat, theta_l[i])) * w_aux - 1], tdeg(op(vars))]
           ) 
        ]:
      end do:
    end if:

    for i from 1 to nops(theta_l) do
      if gb[i] = [1] then
        theta_g := [op(theta_g), theta_l[i]]:
      else
        if infolevel > 1 then
          LogText(sprintf("%s %a %s %a\n", `Groebner basis corresponding to the parameter `, theta_l[i], ` is `, gb[i]), output_targets[log]):
        end if:
      end if:
    end do:    
  elif method = 2 then
     LogText(sprintf("%s %a\n", `Computing Groebner Basis with characteristic`, char), output_targets[log]):
    	gb := Groebner[Basis]([op(Et_hat), z_aux * Q_hat - 1], tdeg(op(vars)), characteristic=char);
    # LogExpression(sprintf("%a", gb), output_targets[log]):
     for i from 1 to nops(theta_l) do
      # LogExpression(sprintf("%a -> %a", Groebner[NormalForm](theta_l[i], gb, tdeg(op(vars)), characteristic=char),  subs(theta_hat, theta_l[i]) mod char), output_targets[log]):
       if char>0 then
       	check := subs(theta_hat, theta_l[i]) mod char:
       else
       	check := subs(theta_hat, theta_l[i]):
       end if:
       if Groebner[NormalForm](theta_l[i], gb, tdeg(op(vars)), characteristic=char) = check then
         theta_g := [ op(theta_g), theta_l[i] ]:
       end if:
     end do:

    if count_solutions then
     LogParameters("",output_targets[parameters]):
    	for var in theta_g do
 		LogText(sprintf("%s %a, %s %a\n",`The number of solutions for`, var, `is`, 1), output_targets[log]):
		LogParameters(sprintf("%s %a, %s %a\n",`Parameter`, ParamToOuter(var, all_vars), `number of solutions:`, 1), output_targets[parameters]):
		solutions_table[var]:=1:
    	end do:
	
    	for var in select(p -> not p in theta_g, theta_l) do
		G := Groebner[Walk](gb, tdeg(op(vars)), lexdeg([op({op(vars)} minus {var})], [var]), characteristic=char):
		P := select(x->evalb(indets(x)={var}), G):
		solutions_table[var]:=degree(P[1], [op(indets(P))]): 
		LogText(sprintf("%s %a, %s %a\n",`The number of solutions for`, var, `is`, degree(P[1], [op(indets(P))])), output_targets[log]):
		LogParameters(sprintf("%s %a, %s %a\n",`Parameter`, ParamToOuter(var, all_vars), `number of solutions:`, degree(P[1], [op(indets(P))])),  output_targets[parameters])
    	end do:
     fi:
    	DocumentTools:-SetProperty(output_targets[globalparams], value,  [op(map(x -> ParamToOuter(x, all_vars), theta_g))], 'refresh'): # global
  else
    LogText(sprintf(`No such method`), output_targets[log]):
    LogText(sprintf("%q\n", "Provided method: %d, allowed methods: 1, 2", method), output_targets[log]):
  end if:

  if infolevel > 0 then
    LogText(sprintf("\n=== Summary ===\n"), output_targets[log]):
    LogText(sprintf("%s %a\n", `Globally identifiable parameters:                 `, map(x -> ParamToOuter(x, all_vars), theta_g)), output_targets[log]):
    LogText(sprintf("%s %a\n", `Locally but not globally identifiable parameters: `, map(x -> ParamToOuter(x, all_vars), select(p -> not p in theta_g, theta_l))), output_targets[log]):
    LogText(sprintf("%s %a\n", `Not identifiable parameters:                      `, map(x -> ParamToOuter(x, all_vars), select(p -> not p in theta_l, theta))), output_targets[log]):
    LogText(sprintf("===============\n\n"), output_targets[log]):
  end if:
  out_sian := table([
    globally = [op(map(x -> ParamToOuter(x, all_vars), theta_g))],
    locally_not_globally = {op(map(x -> ParamToOuter(x, all_vars), select(p -> not p in theta_g, theta_l)))},
    non_identifiable = {op(map(x -> ParamToOuter(x, all_vars), select(p -> not p in theta_l, theta)))},
    parameters = mu,
    basis=gb,
    varordering=tdeg(op(vars)),
    allvars=vars,
    for_outer=all_vars
  ]):
  PrintHeader("WARNING: The result of solution counting is guaranteed with high probability, however it NOT the same probability 'p' as provided in the input."):
  out_sian[num_solutions] := solutions_table:
  return out_sian;
end proc:

#===============================================================================
PrintHeader := proc(text):
#===============================================================================
  LogText(sprintf("\n=======================================================\n"), "LogAreaSIAN"):
  LogText(sprintf(text), "LogAreaSIAN"):
  LogText(sprintf("\n=======================================================\n"), "LogAreaSIAN"):
end proc:

#===============================================================================
GetParameters := proc(system_ODEs, initial_conditions) local initial_values, all_symbols_rhs, mu:
#===============================================================================
  initial_values := map(f -> subs({t = 0}, int(f, t)), select( f -> type(int(f, t), function(name)), map(lhs, system_ODEs) )):
  all_symbols_rhs := foldl(`union`, op( map(e -> indets(rhs(e)), system_ODEs) )) minus {t}:
  mu := select(s -> not type(s, function), all_symbols_rhs):
  if initial_conditions then
    return [op(mu), op(initial_values)]:
  else
    return [op(mu)]:
  end if:
end proc:

#===============================================================================
FunctionToVariable := proc(f):
#===============================================================================
  convert(cat(convert(f, string)[1..-4], "_"), symbol):
end proc:

#===============================================================================
ParamToInner := proc(p) local s:
#===============================================================================
  s := convert(p, string):
  if length(s) > 3 and s[-3..-1] = "(0)" then
    MakeDerivative(FunctionToVariable(p), 0):
  else
    p:
  end if:
end proc:

#===============================================================================
ParamToOuter := proc(p, varnames) local s:
#===============================================================================
  s := convert(p, string):
  if length(s) > 2 and s[-2..-1] = "_0" and parse(s[1..-2] )in varnames then
    parse(cat(s[1..-3], "(0)")):
  else
    p:
  end if:
end proc:

#===============================================================================
MakeDerivative := proc(var_name, der_order):
#===============================================================================
  cat(var_name, der_order):
end proc:


#===============================================================================
DifferentiateOnce := proc(diff_poly, var_list) 
#===============================================================================
  local result, aux, v, h, diff_v:
  result := 0:
  for diff_v in indets(diff_poly) do
    aux := GetOrderVar(diff_v):
    # seems that Maple does not have unpacking
    v := aux[1]:
    h := aux[2]:
    if v in var_list then
      result := result + diff(diff_poly, MakeDerivative(v, h)) * MakeDerivative(v, h + 1):
    end if:
  end do:
  simplify(result):
end proc:


#===============================================================================
Differentiate := proc(diff_poly, var_list, ord := 1) 
#===============================================================================
  local result, i;
  result := diff_poly:
  for i from 1 to ord do
    result := DifferentiateOnce(result, var_list):
  end do:
  result:
end proc:


#===============================================================================
GetVars := proc(diff_poly, var_list)
#===============================================================================
  local result;
  result := select(v -> evalb(GetOrderVar(v)[1] in var_list), indets(diff_poly)):
  return result:
end proc:


#===============================================================================
GetOrderVar := proc(diff_var)
#===============================================================================
  local s, v, h;
  if not StringTools[RegMatch]("^(.*_)([0-9]+)$", diff_var, s, v, h) then
    return ["", ""]:
  end if:
  return [parse(v), parse(h)]:
end proc:


#===============================================================================
SamplePoint := proc(bound, x_vars, y_vars, u_vars, mu, X_eq, Y_eq, Q)
#===============================================================================
  local n, m, s, all_params, all_vars, theta_hat, u_variables, 
        u_hat, x_hat, y_hat, eq, eq_num, eq_denom, 
        v, poly, i, j, all_subs, roll, to_compute;
  n := nops(x_vars):
  m := nops(y_vars):
  s := nops(mu) + n:
  all_params := [op(mu), op(map(x -> MakeDerivative(x, 0), x_vars ))]:
  all_vars := [ op(x_vars), op(y_vars), op(u_vars) ]:

  roll := rand(0 .. bound):
  while true do
    theta_hat := map(p -> p = roll(), all_params): 
    u_variables := [];
    for i from 1 to nops(u_vars) do
      u_variables := [ op(u_variables), seq(MakeDerivative(u_vars[i], j), j = 0..s + 1) ]:
    end do:
    u_hat := map(p -> p = roll(), u_variables) :   
  
    all_subs := [op(theta_hat), op(u_hat)]:
    if subs(all_subs, Q) = 0 then
      next
    end if:
    to_compute := [op(X_eq), op(Y_eq)]:
    while nops(to_compute) <> 0 do
      to_compute := map(e -> lhs(e) = subs(all_subs, rhs(e)), to_compute);
      all_subs := [ op(all_subs), op(select(e -> type(rhs(e), numeric), to_compute)) ]:
      to_compute := remove(e -> type(rhs(e), numeric), to_compute):
    end do:
    y_hat := map(e -> lhs(e) = subs(all_subs, rhs(e)), Y_eq):
    x_hat := map(e -> lhs(e) = subs(all_subs, rhs(e)), X_eq):
    break:
  end do:

  return [y_hat, u_hat, theta_hat, all_subs];
end proc:

#===============================================================================
GenerateReplica := proc(equations, r)
#===============================================================================
  # generates a system of equations corresponding to r independent trajectories of
  # the original system. Time-dependent variabes are replicated, parameters are not
  local all_functions, zero_order, first_order, funcs, without_t, result, i, subst:
  all_functions := select(f -> type(f, function), foldl(`union`, op( map(indets, equations) ))):
  zero_order := select(f -> not type(int(f, t), function(name)), all_functions):
  first_order := map(f -> int(f, t), select(f -> type(int(f, t), function(name)), all_functions)):
  funcs := {op(zero_order), op(first_order)}:
  without_t := map(f -> convert(convert(f, string)[1..-4], symbol), funcs):
  result := []:
  for i from 1 to r do
    subst := map(f -> f = convert(cat(convert(f, string), "_r", i), symbol), without_t):
    result := [op(result), op(map(e -> subs(subst, e), equations))]:
  end do: 
  return result:
end proc:

#===============================================================================
CompareDiffVar := proc(dvl, dvr, var_list)
#===============================================================================
  local vl, vr, hl, hr;
  vl, hl := op(GetOrderVar(dvl, var_list)):
  vr, hr := op(GetOrderVar(dvr, var_list)):
  if evalb(hl <> hr) then
    return evalb(hl > hr):
  end if:
  if evalb(length(vl) <> length(vr)) then
    return evalb(length(vl) > length(vr)):
  end if:
  return StringTools[Compare](vr, vl):
end proc:


LogText:= proc(text, target)
	# must pass text as sprintf(text)!!!
	UpdateLog(text, target);
end proc:

LogExpression:= proc(text, target)
	# must pass text as sprintf("%q\n", text)!!!
	UpdateLog(text, target);
end proc:

#LogTextSIAN := ()->UpdateLog(sprintf(_passed), "LogAreaSIAN");
#LogExpressionSIAN := ()->UpdateLog(sprintf("%q\n", _passed), "SIAN");

#LogTextME := ()->UpdateLog(sprintf(_passed), "LogAreaME");
#LogExpressionME := ()->UpdateLog(sprintf("%q\n", _passed), "LogAreaME");

#LogTextSE := ()->UpdateLog(sprintf(_passed), "LogAreaSE");
#LogExpressionSE := ()->UpdateLog(sprintf("%q\n", _passed), "LogAreaSE");

UpdateLog := proc(s, target)
local logsofar;

	logsofar := DocumentTools:-GetProperty(target, value);
	if logsofar <> "" then
		logsofar := logsofar, "\n";
	end if;
	
	DocumentTools:-SetProperty(target, value, cat(logsofar,s), 'refresh');

end proc:

examples := table([  
  	"Biohydrogenation" = [ "Taken from R. Munoz-Tamayo, L. Puillet, J.B. Daniel, D. Sauvant, O. Martin, M. Taghipoor, P. Blavy\n Review: To be or not to be an identifiable model. Is this a relevant question in animal science modelling?\ndoi.org/10.1017/S1751731117002774\nSystem (3) in Supplementary Material 2, initial conditions are assumed to be unknown",
  	[
  "dx4/dt = - k5 * x4 / (k6 + x4);\n",
  "dx5/dt = k5 * x4 / (k6 + x4) - k7 * x5/(k8 + x5 + x6);\n",
  "dx6/dt = k7 * x5 / (k8 + x5 + x6) - k9 * x6 * (k10 - x6) / k10;\n",
  "dx7/dt = k9 * x6 * (k10 - x6) / k10;\n",
  "y1 = x4;\n",
  "y2 = x5"]],

  	"Chemical Reaction Network" = ["Example 6.1 in the paper 'Global Identifiability of Differential Models'\nTaken from  Conradi, C., Shiu, A., Dynamics of post-translational modification systems: recent progress and future directions Eq. 3.4)",
	[
  "dx1/dt = -k1 * x1 * x2 + k2 * x4 + k4 * x6;\n",
  "dx2/dt = k1 * x1 * x2 + k2 * x4 + k3 * x4;\n",
  "dx3/dt = k3 * x4 + k5 * x6 - k6 * x3 * x5;\n",
  "dx4/dt = k1 * x1 * x2 - k2 * x4 - k3 * x4;\n",
  "dx5/dt = k4 * x6 + k5 * x6 - k6 * x3 * x5;\n",
  "dx6/dt = -k4 * x6 - k5 * x6 + k6 * x3 * x5;\n",
  "y1 = x3;\n"
  "y2 = x2;\n" ]],

	"DAISY Ex. 3" = ["DAISY Example 3", [
  "dx1/dt = -1 * p1 * x1 + x2 + u0;\n",
  "dx2/dt = p3 * x1 - p4 * x2 + x3;\n",
  "dx3/dt = p6 * x1 - p7 * x3;\n",
  "du0/dt = 1;\n",
  "y1 = x1;\n",
  "y2 = u0;\n"]],

	"DAISY_mamil3" = ["DAISY mamil 3",
	[
  "dx1/dt = -(a21 + a31 + a01) * x1 + a12 * x2 + a13 * x3 + u(t);\n",
  "dx2/dt = a21 * x1 - a12 * x2;\n",
  "dx3/dt = a31 * x1 - a13 * x3;\n",
  "y = x1"]],
  
	"DAISY_mamil4" = ["DAISY mamil 4", [
  "dx1/dt = -k01 * x1 + k12 * x2 + k13 * x3 + k14 * x4 - k21 * x1 - k31 * x1 - k41 * x1 + u(t);\n",
  "dx2/dt = -k12 * x2 + k21 * x1;\n",
  "dx3/dt = -k13 * x3 + k31 * x1;\n",
  "dx4/dt = -k14 * x4 + k41 * x1;\n",
  "y = x1"]],

	"HIV" = ["Example (with initial conditions assumed being unknown) from Section IV of 'DAISY: an Efficient Tool to Test Global Identifiability. Some Case Studies' by G. Bellu, M.P. Saccomani",
	[
  "dx1/dt = -beta * x1 * x4 - d * x1 + s;\n",
  "dx2/dt = beta * q1 * x1 * x4 - k1 * x2 - mu1 * x2;\n",
  "dx3/dt = beta * q2 * x1 * x4 + k1 * x2 - mu2 * x3;\n",
  "dx4/dt = -c * x4 + k2 * x3;\n",
  "y1 = x1;\n",
  "y2 = x4"]],

	"HIV2" = ["The system is taken from Wodarz, D., Nowak, M.\nMathematical models of HIV pathogenesis and treatment\nSystem (6)",
	[
  "dx/dt = lm - d * x - beta * x * v;\n",
  "dy/dt = beta * x * v - a * y;\n",
  "dv/dt = k * y - u * v;\n",
  "dw/dt = c * x * y * w - c * q * y * w - b * w;\n",
  "dz/dt = c * q * y * w - h * z;\n",
  "y1 = w;\n",
  "y2 = z"]],

	"Lipolysis" = ["Taken from R. Munoz-Tamayo, L. Puillet, J.B. Daniel, D. Sauvant, O. Martin, M. Taghipoor, P. Blavy\nReview: To be or not to be an identifiable model. Is this a relevant question in animal science modelling?\ndoi.org/10.1017/S1751731117002774\nSystem (1) in Supplementary Material 2, initial conditions are assumed to be unknown\nbrought to the rational function form by introducing new state variable x5 = k1 e^(-k3 t)",
	[
  "dx1/dt = -x1 * x5 / (k2 + x1);\n",
  "dx2/dt = 2 * x1 * x5 / ((k2 + x1) * 3) - k4 * x2;\n",
  "dx3/dt = k4*(x2)/2 - k4*x3;\n",
  "dx4/dt = x1 * x5 / (3 * (k2 + x1)) + k4 * (x2)/2 + k4 * x3;\n",
  "dx5/dt = -k3 * x5;\n",
  "y1 = x1;\n",
  "y2 = x2 + x3;\n",
  "y3 = x4"]],

  	"LV" = ["",[
  	"dx1/dt = a*x1 - b*x1*x2;\n", 
  	"dx2/dt = -c*x2 + d*x1*x2;\n",
  	"y = x1 + u(t);\n"]],
	"OralGlucose" = ["Example (with initial conditions assumed being unknown) from Section III of 'DAISY: an Efficient Tool to Test Global Identifiability. Some Case Studies'\nby G. Bellu, M.P. Saccomani",
	[
  "dG/dt = -(p1 + X) * G + p1 * Gb + v * R;\n",
  "dX/dt = -p2 * X + p3 * (u(t) - Ib);\n",
  "dR/dt = k;\n",
  "dIb/dt = 0;\n",
  "dGb/dt = 0;\n",
  "y1 = G;\n",
  "y2 = Ib;\n",
  "y3 = Gb;\n"]],

	"SEIR" = ["Taken from N. Tuncer, T. Le\n'Structural and practical identifiability analysis of outbreak models'\nhttps://doi.org/10.1016/j.mbs.2018.02.004\nEquation (2.2) with prevalence observations",
[
  "dS/dt = -b * S * In / N;\n",
  "dE/dt = b * S * In / N - nu * E;\n",
  "dIn/dt = nu * E - a * In;\n",
  "dN/dt = 0;\n",
  "y1 = In;\n",
  "y2 = N;\n"]],

	"SEIR2" = ["Taken from N. Tuncer, T. Le\n'Structural and practical identifiability analysis of outbreak models'\nhttps://doi.org/10.1016/j.mbs.2018.02.004\nEquation (2.2) with cumulative incidence observations",
	[
  "dS/dt = -b * S * In / N;\n",
  "dE/dt = b * S * In / N - nu * E;\n",
  "dIn/dt = nu * E - a * In;\n",
  "dN/dt = 0;\n",
  "dCu/dt = nu * E;\n",
  "y1 = Cu;\n",
  "y2 = N"]],

	"SIR_R0" = ["SIR R0",[
  "dS/dt = -b * In * S;\n",
  "dIn/dt = b * In * S - g * In;\n",
  "dR/dt = g * In;\n",
  "daux/dt = 0;\n",
  "y1 = In;\n",
  "y2 = b / g + aux;"]],

	"SIRSForced" = ["Taken from Capistran M., Moreles M., Lara B.\n'Parameter Estimation of Some Epidemic Models.\n The Case of Recurrent Epidemics Caused by Respiratory Syncytial Virus'\ndoi.org/10.1007/s11538-009-9429-3\nEquations (7)-(11)",
[
  "ds/dt = mu - mu * s - b0 * (1 + b1 * x1) * i * s + g * r;\n",
  "di/dt = b0 * (1 + b1 * x1) * i * s - (nu + mu) * i;\n",
  "dr/dt = nu * i - (mu + g) * r;\n",
  "dx1/dt = -M * x2;\n",
  "dx2/dt = M * x1;\n",
  "y1 = i;\n",
  "y2 = r;\n"]],

	"SlowFast" = ["Taken from Vajda S., Rabitz H.\n'Identifiability and Distinguishability of First-Order Reaction Systems', p. 701\nWe added an extra output x_C",
	[
  "dxA/dt = -k1 * xA;\n",
  "dxB/dt = k1 * xA - k2 * xB;\n",
  "dxC/dt = k2 * xB;\n",
  "deA/dt = 0;\n",
  "deC/dt = 0;\n",
  "y1 = eA * xA + eB * xB + eC * xC;\n",
  "y2 = xC;\n",
  "y3 = eA;\n",
  "y4 = eC"]],
	
	"Treatment" = ["Taken from N. Tuncer, T. Le\nStructural and practical identifiability analysis of outbreak models'\nhttps://doi.org/10.1016/j.mbs.2018.02.004\nEquation (2.3) with observed treatment",
	[
  "dS/dt = -b * S * In / N - d * b * S * Tr / N;\n",
  "dIn/dt = b * S * In / N + d * b * S * Tr / N - (a + g) * In;\n",
  "dTr/dt = g * In - nu * Tr;\n",
  "dN/dt = 0;\n",
  "y1 = Tr;\n",
  "y2 = N"]],

	"Tumor" = ["Example (with initial conditions assumed being unknown) from Section 3 of\n'Examples of testing global identifiability of biological and biomedical models with the DAISY software'\nby M.P. Saccomani, S. Audoly, G. Bellu, L. D'Angio",
[ "dx1/dt = -(k3 + k7) * x1 + k4 * x2;\n",
  "dx2/dt = k3 * x1 - (k4 + a * k5 + b * d1 * k5) * x2 + k6 * x3 + k6 * x4 + k5 * x2 * x3 + k5 * x2 * x4;\n",
  "dx3/dt = a * k5 * x2 - k6 * x3 - k5 * x2 * x3;\n",
  "dx4/dt = b * d1 * k5 * x2 - k6 * x4 - k5 * x2 * x4;\n",
  "dx5/dt = k7 * x1;\n",
  "da/dt = 0;\n",
  "db/dt = 0;\n",
  "dd1/dt = 0;\n",
  "y1 = x5;\n",
  "y2 = a;\n",
  "y3 = b;\n",
  "y4 = d1;\n"]]
]):

# Setup

timed_SIAN:=proc(sigma, params_to_assess, p, output_targets_sian, count_solutions, char)
	local output, data, start, finish:
	start:= time():
	output := IdentifiabilityODE(sigma, params_to_assess, p, output_targets_sian, count_solutions, char):
	finish:= time():
	DocumentTools:-SetProperty(output_targets_sian[runningtime], value, convert(finish-start, string), 'refresh'): # time
	return  output:
end proc:

timed_Multi:=proc(model, simplified_generators, no_bound, simplify_bound, max_perms, output_targets_multi)
	local start, output, finish, data:
	start:=time():
	bound, generators := op(MultiExperimentIdentifiableFunctions(model, simplified_generators, no_bound, simplify_bound, max_perms, output_targets_multi)):
	finish:=time():
	DocumentTools:-SetProperty(output_targets_multi[runningtime], value, convert(finish-start, string), 'refresh'):
	return [bound, finish-start, generators]: #table([output=bound, runtime=finish-start]):
end proc:

timed_Single:=proc(model, output_targets_single)
	local start, output, finish, data:
	start:=time():
	output := SingleExperimentIdentifiableFunctions(model, output_targets_single):
	finish:=time():
	DocumentTools:-SetProperty(output_targets_single[runningtime], value, convert(finish-start, string), 'refresh'):
	return output:
end proc:

with(StringTools):

sigmaParser := proc(sigma)
	local states, state_eqs, outputs, output_eqs;
	if SearchText("diff", sigma)>0 then
		sigma := [map(x->parse(x), Split(sigma, ";"))]:
	else
		LogExpression(sprintf("%q \n", Split(sigma, ";")), "LogAreaSIAN"):
		sigma := Split(sigma, ";"):
		
		states := map(x->Trim(RegSubs("d([a-zA-Z0-9]+)/dt(.*)" = "\\1", x)), select(x->SearchText(x, "/dt")>0, sigma)):
		state_eqs := select(x->Has(x, "/dt"), sigma):
		
		outputs :=  map(x->Trim(Split(x, "=")[1]), select(x->not Has(x, "/dt"), sigma)):
		output_eqs := select(x->not SearchText(x, "/dt")>0, sigma):
		
		state_eqs := map(x->convert(subs({seq(parse(states[i])=parse(cat(states[i],"(t)")), i=1..nops(states))}, parse(x)), string),  state_eqs):
		state_eqs := map(x->parse(RegSubs("d([a-zA-Z0-9]+)/dt(.*)" = "diff(\\1(t), t)\\2", x)), state_eqs):
	
		output_eqs := map(x->parse(Subs({seq(outputs[i]=cat(outputs[i],"(t)"), i=1..nops(outputs))}, x)), output_eqs):	
		output_eqs := map(x->subs({seq(parse(states[i])=parse(cat(states[i],"(t)")), i=1..nops(states))}, x),  output_eqs):
		
		sigma := [op(state_eqs), op(output_eqs)]:
	end if:
	return sigma;
end proc:


DocumentTools:-SetProperty("RunningTimeSingle", value, ""):
DocumentTools:-SetProperty("RunningTimeMulti", value, ""):
DocumentTools:-SetProperty("RunningTimeSIAN", value, ""):

DocumentTools:-SetProperty("run_system", enabled, true):
DocumentTools:-SetProperty("Meter_sian", visible, true):
DocumentTools:-SetProperty("Meter_sian", value, 0):
DocumentTools:-SetProperty("sigma", enabled, true):
DocumentTools:-SetProperty("p", value, "0.99"):
DocumentTools:-SetProperty("params", value, ""):
DocumentTools:-SetProperty("replicas", value, "1"):

DocumentTools:-SetProperty("p", enabled, true):
DocumentTools:-SetProperty("params", enabled, true):
DocumentTools:-SetProperty("replicas", enabled, true):
DocumentTools:-SetProperty("LogAreaSE", value, ""):
DocumentTools:-SetProperty("LogAreaSIAN", value, ""):
DocumentTools:-SetProperty("LogAreaME", value, ""):

DocumentTools:-SetProperty("printSolutions", enabled, true):
DocumentTools:-SetProperty("printSolutions", value, true):

DocumentTools:-SetProperty("GlobalParams1", expression, NULL):
DocumentTools:-SetProperty("LocalParams1", expression, NULL):
DocumentTools:-SetProperty("NoIDParams1", expression, NULL):

DocumentTools:-SetProperty("Parameters", value, ""):

DocumentTools:-SetProperty("Bound", expression, NULL):
DocumentTools:-SetProperty("MultiFunctions", expression, NULL):
DocumentTools:-SetProperty("SingleFunctions", expression, NULL):

DocumentTools:-SetProperty("use_char", enabled, true):
DocumentTools:-SetProperty("use_char", value, false):
DocumentTools:-SetProperty("p_label", enabled, true):

DocumentTools:-SetProperty("ComputeId", enabled, true):
DocumentTools:-SetProperty("ComputeId", value, false):
DocumentTools:-SetProperty("bypass", enabled, false):

DocumentTools:-SetProperty("bypass", value, true):
DocumentTools:-SetProperty("SimplifiedGen", enabled, false):
DocumentTools:-SetProperty("SimplifiedGen", value, true):
DocumentTools:-SetProperty("SkipSingle", enabled, false):
DocumentTools:-SetProperty("SkipSingle", value, false):
DocumentTools:-SetProperty("Refine", enabled, false):
DocumentTools:-SetProperty("NoBound", enabled, false):
DocumentTools:-SetProperty("NoBound", value, false):
DocumentTools:-SetProperty("UsingUpTo", enabled, false):
DocumentTools:-SetProperty("MaxPermutations", enabled, false):
DocumentTools:-SetProperty("Permutations", enabled, false):
DocumentTools:-SetProperty("RunSIAN", enabled, true):
DocumentTools:-SetProperty("RunSIAN", value, true):
DocumentTools:-SetProperty("being_refined", caption, "");
DocumentTools:-SetProperty("sigma", value, "dx1/dt = a*x1 + x2*b + u(t);\ndx2/dt = x2*c + x1;\ny=x2"):
DocumentTools:-SetProperty("example_box", value, "Custom"):
