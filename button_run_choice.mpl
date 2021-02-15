 use DocumentTools in 
	 	

	
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
	ClearLog("Parameters1"):
	SetProperty("LogAreaSIAN", value, ""):
	SetProperty("LogAreaSE", value, ""):
	SetProperty("LogAreaME", value, ""):
	SetProperty("GlobalParams", expression, Running):
	SetProperty("LocalParams", expression, Running):
	SetProperty("NoIDParams", expression, Running):
	SetProperty("being_refined1", caption, ""):


	
	SetProperty("Meter_example", value, 100):
	SetProperty("RunningTimeSIAN1", value, ""):
	SetProperty("RunningTimeSingle1", value, ""):
	SetProperty("RunningTimeMulti1", value, ""):
	run_single:= parse(GetProperty("RunSingle1", value)):
	run_multi:= parse(GetProperty("RunMulti1", value)):	
	simplified_generators:= parse(GetProperty("SimplifiedGen1", value)):
	simplify_bound := parse(GetProperty("Refine1", value)):
	no_bound:= parse(GetProperty("NoBound1", value)):
	
	if run_multi then
		if not no_bound then
			SetProperty("Bound1", expression, Running):
		fi:
		SetProperty("MultiFunctions1", expression, Running):
	end if:
	if run_single then
		SetProperty("SingleFunctions1", expression, Running):
	fi:
	output_targets_multi:=["MultiFunctions1", "Bound1", "RunningTimeMulti1", "SingleFunctions1", run_single, "RunningTimeSingle1"]:
	output_targets_single:=["SingleFunctions1","RunningTimeSingle1"]:
	output_targets_sian:=["GlobalParams","LocalParams", "NoIDParams", "RunningTimeSIAN1"]:

	model := examples[exname][2]:#[seq(lhs(e) - rhs(e), e in examples[exname][2])]:
	LogExpression(sprintf("%q \n", model), "LogAreaSIAN"):
	out_sian := IdentifiabilityODE(examples[exname][2],  GetParameters(examples[exname][2], true), 0.99, output_targets_sian):

	basis_sian:=out_sian[basis]:
	ordering_sian:=out_sian[varordering]:
	all_other:=out_sian[allvars]:
	output_expression := "":
	LogParameters("","Parameters1"):
	
	for var in map(ParamToInner, out_sian[globally]) do
	 	LogText(sprintf("%s %a %s %a\n",`The number of solutions for`, var, `is`, 1), "LogAreaSIAN"):
		LogParameters(sprintf("%s %a %s %a\n",`Parameter`, ParamToOuter(var, out_sian[for_outer]), `, number of solutions: `, 1), "Parameters1"):
	end do:
	
	for var in map(ParamToInner, out_sian[locally_not_globally]) do 
		G := Groebner[Walk](basis_sian, ordering_sian, lexdeg([op({op(all_other)} minus {var})], [var])):
		P := select(x->evalb(indets(x)={var}), G):
	 	LogText(sprintf("%s %a %s %a\n",`The number of solutions of`, ParamToOuter(var, out_sian[for_outer]), `is`, degree(P[1], [op(indets(P))])), "LogAreaSIAN"):
		LogParameters(sprintf("%s %a %s %a\n",`Parameter`, ParamToOuter(var, out_sian[for_outer]), `, number of solutions: `, degree(P[1], [op(indets(P))])), "Parameters1")
	end do:
	
	identified_params:=select(x->evalb(x in out_sian[parameters]), out_sian[globally]):
	
	if nops(identified_params)=nops(out_sian[parameters]) then
		run_multi:=false;
		SetProperty("Bound1", value, 1):
		SetProperty("MultiFunctions1", value, convert(out_sian[parameters], list)):
		run_single:=false:
		SetProperty("SingleFunctions1", value, convert(out_sian[parameters], list)):
	fi:

	max_perms:= parse(GetProperty("MaxPermutations1", value)):
	
	if run_multi then
		out_multi := MultiExperimentIdentifiableFunctions(model, simplified_generators, no_bound, simplify_bound, output_targets_multi, max_perms):
	fi:

	if out_multi[bd]=1 then
		run_single:=false:
	fi:		
	if run_single then
		out_single := SingleExperimentIdentifiableFunctions(model, output_targets_single, infolevel=1):
	fi:

	
	
	#Grid[Setup]("local", numnodes = 3):

	#Grid:-Run(0, timed_SIAN, [examples[exname][2],  GetParameters(examples[exname][2], true), 0.99, output_targets_sian], set= {timed_SIAN}, assignto='out_sian'):

	#Grid:-Run(1, timed_Single, [model, run_single, output_targets_single], set= {timed_Single}, assignto='out_single'):

	#Grid:-Run(2, timed_Multi, [model, simplified_generators, no_bound, run_multi, output_targets_multi], set= {timed_Multi}, assignto='out_multi', wait=true):

	#SetProperty("GlobalParams", expression, out_sian[globally]):
	#LogExpression(out_multi):
	#LogExpression(out_single):
	SetProperty("Meter_example", value, 0):
end use; 
