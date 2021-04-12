with(DocumentTools):
with(StringTools):

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

SetProperty("RunningTimeSIAN", value, ""):
SetProperty("RunningTimeMulti", value, ""):
SetProperty("RunningTimeSingle", value, ""):

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

skip_single:= parse(GetProperty("SkipSingle", value)):
computeId:= parse(GetProperty("ComputeId", value)):

simplified_generators := parse(GetProperty("SimplifiedGen", value)):
simplify_bound := parse(GetProperty("Refine", value)):
no_bound:= parse(GetProperty("NoBound", value)):
use_char := parse(GetProperty("use_char", value)):
err := 0:
#try:
	sigma:="":
	sigma:=GetProperty("sigma", value):
	if SearchText("diff", sigma)>0 then
		LogText(sprintf("%q\n", "Using Maple input format"), "LogAreaSIAN"):
		sigma := map(x->parse(x), Split(sigma, ";")):
	else
		LogText(sprintf("Using text-based input format"), "LogAreaSIAN"):
		sigma := Split(sigma, ";"):
		states := map(x->Trim(RegSubs("d([a-zA-Z0-9]+)/dt(.*)" = "\\1", x)), select(x->Search("/dt", x)>0, sigma)):
		state_eqs := select(x->Search("/dt", x)>0, sigma):
		
		outputs :=  map(x->Trim(Split(x, "=")[1]), select(x-> not Search("/dt", x)>0, sigma)):
		output_eqs := select(x->not Search("/dt", x)>0, sigma):
		
		state_eqs := map(x->convert(subs({seq(parse(states[i])=parse(cat(states[i],"(t)")), i=1..nops(states))}, parse(x)), string),  state_eqs):
		state_eqs := map(x->parse(RegSubs("d([a-zA-Z0-9]+)/dt(.*)" = "diff(\\1(t), t)\\2", x)), state_eqs):
	
		output_eqs := map(x->parse(Subs({seq(outputs[i]=cat(outputs[i],"(t)"), i=1..nops(outputs))}, x)), output_eqs):	
		output_eqs := map(x->subs({seq(parse(states[i])=parse(cat(states[i],"(t)")), i=1..nops(states))}, x),  output_eqs):
		
		sigma := [op(state_eqs), op(output_eqs)]:
	end if:
	LogExpression(sprintf("%q \n", sigma), "LogAreaSIAN"):
(*catch:
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
end try:*)

#try:
	params_to_assess := [seq(parse(expr), expr in StringTools[Split](GetProperty("params", value), ";"))]:
	LogExpression(sprintf("%q \n", params_to_assess), "LogAreaSIAN"):
(*catch:
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
end try:*)

#try:
	replicas := parse(GetProperty("replicas", value)):
	if replicas <=1 then
		initial_conditions:= true:
	else
		sigma := GenerateReplica(sigma, replicas):
		initial_conditions:=false:
	end if:
	
	if nops(params_to_assess)=0 then
		LogText(sprintf("%q\n", "Checking all parameters"), "LogAreaSIAN"):
		params_to_assess := GetParameters(sigma, initial_conditions):
	end if:
	p:=parse(GetProperty("p", value)):
	
(*catch:
	SetProperty("LogAreaSIAN", value, "SYNTAX ERROR PLEASE CHECK INPUTS"): # LogText(
	err:=1:
	SetProperty("GlobalParams1", expression, Error("see Logs")):
	SetProperty("LocalParams1", expression, Error("see Logs")):
	SetProperty("NoIDParams1", expression, Error("see Logs")):
	SetProperty("Bound", expression, Error("see Logs")):
	SetProperty("MultiFunctions", expression, Error("see Logs")):
	SetProperty("SingleFunctions", expression, Error("see Logs")):
	SetProperty("Meter_sian", value, 0):
end try:*)

if err=0 then
	run_sian := parse(GetProperty("RunSIAN", value)):
	if run_sian then
		SetProperty("GlobalParams1", expression, Running):
		SetProperty("LocalParams1", expression, Running):
		SetProperty("NoIDParams1", expression, Running):
	fi:
	if computeId then
		if not no_bound then
			SetProperty("Bound", expression, Running):
		fi:
		if not skip_single then
			SetProperty("SingleFunctions", expression, Running):
		fi:	
		SetProperty("MultiFunctions", expression, Running):
	end if:
	

	output_targets_multi:=table([log="LogAreaME", multi="MultiFunctions", bound_="Bound", runningtime="RunningTimeMulti", single="SingleFunctions",
					  	    run_single_=run_single, runningtimesingle="RunningTimeSingle"]):
	output_targets_single:=table([log="LogAreaSE", single="SingleFunctions", runningtime="RunningTimeSingle"]):
	output_targets_sian:=table([globalparams="GlobalParams1", localparams= "LocalParams1", noidparams="NoIDParams1", 
						   runningtime="RunningTimeSIAN", log="LogAreaSIAN", parameters="Parameters"]):
	bypass_ := parse(GetProperty("bypass", value)):

	count_solutions := parse(GetProperty("printSolutions", value)):

	if run_sian then
		if use_char then
			char := 2^29 -3:
		else
			char := 0:
		end if:
		out_sian := timed_SIAN(sigma,  params_to_assess, 0.99, output_targets_sian, count_solutions, char):
		basis_sian:=out_sian[basis]:
		ordering_sian:=out_sian[varordering]:
		all_other:=out_sian[allvars]:
		identified_params:=select(x->evalb(x in out_sian[parameters]), out_sian[globally]):
		max_perms:= parse(GetProperty("MaxPermutations", value)):
		if bypass_ then
			if nops(identified_params)=nops(out_sian[parameters]) then
				if computeId then
					LogText(sprintf("Bypassing Multi-Experiment check via SIAN"), "LogAreaME"):
				end if:
				computeId:=false;
				se_me_bypass_time := time():
				SetProperty("Bound", value, 1):
				SetProperty("MultiFunctions", value, convert(out_sian[parameters], list)):
				SetProperty("RunningTimeMulti", value, convert(time() - se_me_bypass_time, string), 'refresh'): # time
				
				if not skip_single then
					LogText(sprintf("Bypassing Single-Experiment check via SIAN"), "LogAreaSE"):
				end if:
				skip_single:=true:
				se_me_bypass_time := time():
				SetProperty("SingleFunctions", value, convert(out_sian[parameters], list)):
				SetProperty("RunningTimeSingle", value, convert(time() - se_me_bypass_time, string), 'refresh'): # time
			fi:	
		end if:
	fi:
	if computeId then
		out_multi := timed_Multi(sigma, simplified_generators, no_bound, simplify_bound, max_perms, output_targets_multi):
		generators := convert(out_multi[3],list):
		finish_bypass_multi:=out_multi[2]:
		bound := out_multi[1]: # bound value
		if bound=1  then
			if not skip_single then
				LogText(sprintf("Deterministically bypassing Single-Experiment via Multi-Experiment check, bound from Multi-Experiment = 1"), "LogAreaSE"):
			end if:
			skip_single:=true:
			SetProperty("RunningTimeSingle", value, finish_bypass_multi, 'refresh'): # time
		fi:	
		if not skip_single then
			out_single := timed_Single(sigma, output_targets_single):
			if out_single = generators and bound>1 then
				LogText(sprintf("Deterministically overriding Multi-Experiment via Single-Experiment check,\n bound from Multi-Experiment > 1, single- and multi-experiment generators are the same"), "LogAreaSE"):
				SetProperty("MultiFunctions", value, convert(out_single, list)):
				SetProperty("Bound", value, 1):
			fi:	
			LogExpression(sprintf("%q %q\n",out_single, generators), "LogAreaSE");
		fi:
	fi:
	SetProperty("Meter_sian", value, 0):
end if: