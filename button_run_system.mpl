with(DocumentTools):
SetProperty("Meter_sian", value, 100):
SetProperty("LogAreaSIAN", value, ""):
SetProperty("LogAreaSE", value, ""):
SetProperty("LogAreaME", value, ""):
SetProperty("GlobalParams1", expression, NULL):
SetProperty("LocalParams1", expression, NULL):
SetProperty("NoIDParams1", expression, NULL):
SetProperty("Bound", expression, NULL):
SetProperty("MultiFunctions", expression, NULL):
SetProperty("SingleFunctions", expression, NULL):
SetProperty("being_refined", caption, ""):

LogParameters := proc(s, target)
	local logsofar;
	logsofar := DocumentTools:-GetProperty(target, value);
	if logsofar <> "" then
		logsofar := logsofar, "\n";
	end if;
	DocumentTools:-SetProperty(target, value, cat(logsofar,s), 'refresh');
end proc:

ClearLog := proc(target)

		DocumentTools:-SetProperty(target, value, "");
		
end proc:
ClearLog("Parameters"):

run_single:= parse(GetProperty("RunSingle", value)):
run_multi:= parse(GetProperty("RunMulti", value)):

simplified_generators := parse(GetProperty("SimplifiedGen", value)):
simplify_bound := parse(GetProperty("Refine", value)):
no_bound:= parse(GetProperty("NoBound", value)):

err := 0:
try:
	sigma := [seq(parse(expr), expr in StringTools[Split](GetProperty("sigma", value), ";"))]:
	LogExpression(sprintf("%q \n", sigma), "LogAreaSIAN"):
catch:
	SetProperty("LogAreaSIAN", value, "Error parsing system: check syntax"): # LogText(
	err:=1:
	SetProperty("GlobalParams1", expression, SystemParseError("see Logs")):
	SetProperty("LocalParams1", expression,  SystemParseError("see Logs")):
	SetProperty("NoIDParams1", expression, SystemParseError("see Logs")):
	SetProperty("Bound", expression,  SystemParseError("see Logs")):
	SetProperty("MultiFunctions", expression,  SystemParseError("see Logs")):
	SetProperty("SingleFunctions", expression,  SystemParseError("see Logs")):
	SetProperty("Meter_sian", value, 0):
	error "Error parsing system: check syntax":
end try:

try:
	params_to_assess := [seq(parse(expr), expr in StringTools[Split](GetProperty("params", value), ";"))]:
catch:
	SetProperty("LogAreaSIAN", value, "Error Parsing Parameters"): # LogText(
	err:=1:
	SetProperty("GlobalParams1", expression, ParameterParseError("see Logs")):
	SetProperty("LocalParams1", expression,  ParameterParseError("see Logs")):
	SetProperty("NoIDParams1", expression, ParameterParseError("see Logs")):
	SetProperty("Bound", expression,  ParameterParseError("see Logs")):
	SetProperty("MultiFunctions", expression,  ParameterParseError("see Logs")):
	SetProperty("SingleFunctions", expression,  ParameterParseError("see Logs")):
	SetProperty("Meter_sian", value, 0):
	error "Error parsing parameters: check syntax":
end try:

try:
	replicas := parse(GetProperty("replicas", value)):
	if replicas <=1 then
		initial_conditions:= true:
	else
		sigma := GenerateReplica(sigma, replicas):
		initial_conditions:=false:
	end if:
	
	if nops(params_to_assess)=0 then
		params_to_assess := GetParameters(sigma, initial_conditions):
	end if:
	p:=parse(GetProperty("p", value)):
	
catch:
	SetProperty("LogAreaSIAN", value, "SYNTAX ERROR PLEASE CHECK INPUTS"): # LogText(
	err:=1:
	SetProperty("GlobalParams1", expression, Error("see Logs")):
	SetProperty("LocalParams1", expression, Error("see Logs")):
	SetProperty("NoIDParams1", expression, Error("see Logs")):
	SetProperty("Bound", expression, Error("see Logs")):
	SetProperty("MultiFunctions", expression, Error("see Logs")):
	SetProperty("SingleFunctions", expression, Error("see Logs")):
	SetProperty("Meter_sian", value, 0):
end try:

if err=0 then
	SetProperty("GlobalParams1", expression, Running):
	SetProperty("LocalParams1", expression, Running):
	SetProperty("NoIDParams1", expression, Running):
	if run_multi then
		if not no_bound then
			SetProperty("Bound", expression, Running):
		fi:
		SetProperty("MultiFunctions", expression, Running):
	end if:
	
	if run_single then
		SetProperty("SingleFunctions", expression, Running):
	fi:
	output_targets_multi:=["MultiFunctions", "Bound", "RunningTimeMulti", "SingleFunctions", run_single, "RunningTimeSingle"]:
	output_targets_single:=["SingleFunctions", "RunningTimeSingle"]:
	output_targets_sian:=["GlobalParams1", "LocalParams1", "NoIDParams1", "RunningTimeSIAN"]:

	out_sian := IdentifiabilityODE(sigma,  GetParameters(sigma, initial_conditions), 0.99, output_targets_sian):

	basis_sian:=out_sian[basis]:
	ordering_sian:=out_sian[varordering]:
	all_other:=out_sian[allvars]:
	for var in map(ParamToInner, out_sian[globally]) do
	 	LogText(sprintf("%s %a %s %a\n",`The number of solutions for`, var, `is`, 1), "LogAreaSIAN"):
		LogParameters(sprintf("%s %a %s %a\n",`Parameter`, ParamToOuter(var, out_sian[for_outer]), `, number of solutions: `, 1), "Parameters"):
	end do:
	
	for var in map(ParamToInner, out_sian[locally_not_globally]) do
		G := Groebner[Walk](basis_sian, ordering_sian, lexdeg([op({op(all_other)} minus {var})], [var])):
		P := select(x->evalb(indets(x)={var}), G):
	 	LogText(sprintf("%s %a %s %a\n",`The number of solutions for`, var, `is`, degree(P[1], [op(indets(P))])), "LogAreaSIAN"):
		LogParameters(sprintf("%s %a %s %a\n",`Parameter`, ParamToOuter(var, out_sian[for_outer]), `, number of solutions: `, degree(P[1], [op(indets(P))])), "Parameters")
	end do:
	
	identified_params:=select(x->evalb(x in out_sian[parameters]), out_sian[globally]):
	max_perms:= parse(GetProperty("MaxPermutations", value)):
	if nops(identified_params)=nops(out_sian[parameters]) then
		run_multi:=false;
		SetProperty("Bound", value, 1):
		SetProperty("MultiFunctions", value, convert(out_sian[parameters], list)):	
		run_single:=false:
		SetProperty("SingleFunctions", value, convert(out_sian[parameters], list)):
	fi:

	if run_multi then
		out_multi := MultiExperimentIdentifiableFunctions(sigma, simplified_generators, no_bound, simplify_bound, output_targets_multi, max_perms):
	fi:
	
	if out_multi[bd]=1  then
		run_single:=false:
	fi:		
	if run_single then
		out_single := SingleExperimentIdentifiableFunctions(sigma, output_targets_single, infolevel=1):
	fi:


	
	
	#LogExpression(run_single):
	
	#Grid[Setup]("local", numnodes = 3):

	#Grid:-Run(0, timed_SIAN_local, [sigma,  params_to_assess, p, output_targets_sian], set= {timed_SIAN_local}, assignto='out_sian'):
	
	#Grid:-Run(1, timed_Single, [model, run_single, output_targets_single], set= {timed_Single}, assignto='out_single'):

	#Grid:-Run(2, timed_Multi, [model, simplified_generators, no_bound, run_multi, output_targets_multi], set= {timed_Multi}, assignto='out_multi',  wait=true):

	#SetProperty("GlobalParams1", expression, out_sian[1][globally]):

	#LogExpression(out_multi):
	#LogExpression(out_single):
	#if run_single then
	#	SetProperty("SingleFunctions", expression, out_single):
	#fi:
	SetProperty("Meter_sian", value, 0):
end if: