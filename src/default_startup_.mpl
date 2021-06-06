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

  	"Chemical Reaction Network" = ["Taken from  Conradi, C., Shiu, A., Dynamics of post-translational modification systems: recent progress and future directions Eq. 3.4",
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
  "dx1/dt = -1 * p1 * x1 + p2 * x2 + u(t);\n",
  "dx2/dt = p3 * x1 - p4 * x2 + p5 * x3;\n",
  "dx3/dt = p6 * x1 - p7 * x3;\n",
  "y1 = x1;\n"]],

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
  "dx1/dt = -b * x1 * x4 - d * x1 + s;\n",
  "dx2/dt = b * q1 * x1 * x4 - k1 * x2 - mu1 * x2;\n",
  "dx3/dt = b * q2 * x1 * x4 + k1 * x2 - mu2 * x3;\n",
  "dx4/dt = -c * x4 + k2 * x3;\n",
  "y1 = x1;\n",
  "y2 = x4"]],

	"HIV2" = ["The system is taken from Wodarz, D., Nowak, M.\nSpecific therapy regimes could lead to long-term immunological control of HIV\nhttps://doi.org/10.1073/pnas.96.25.14464\nPage 1",
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

  	"LV" = ["Lotka-Volterra System",[
  	"dx1/dt = a*x1 - b*x1*x2;\n", 
  	"dx2/dt = -c*x2 + d*x1*x2;\n",
  	"y = x1;\n"]],
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
	local start, output, finish, data, bound, generators:
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
DocumentTools:-SetProperty(reference, value, ""):
DocumentTools:-SetProperty("LocalLabel" , caption, "Locally Identifiable Paramters");
DocumentTools:-SetProperty(TxtOutput, visible, false);
DocumentTools:-SetProperty(TxtOutput, value, "");
DocumentTools:-SetProperty(SaveOutputLabel, visible, false);

readyToSave:=false:
counter:=0:
exname:="Custom":