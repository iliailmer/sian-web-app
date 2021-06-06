use DocumentTools in 

SetProperty("sigma", value, ""):
exname := GetProperty("example_box", value):
# cleanup
SetProperty("LogAreaSIAN", value, ""):
SetProperty("LogAreaSE", value, ""):
SetProperty("LogAreaME", value, ""):
SetProperty("GlobalParams1", expression, NULL):
SetProperty("LocalParams1", expression, NULL):
SetProperty("NoIDParams1", expression, NULL):
SetProperty("being_refined", caption, ""):
SetProperty("Bound", expression, NULL):
SetProperty("MultiFunctions", expression, NULL):
SetProperty("SingleFunctions", expression, NULL):
SetProperty("RunningTimeSIAN", value, ""):
SetProperty("RunningTimeMulti", value, ""):
SetProperty("RunningTimeSingle", value, ""):
SetProperty("Parameters", value, ""):

SetProperty("sigma", value, exname):
if exname = "Custom" then
	SetProperty("sigma", value, ""):
else
	SetProperty("sigma", value,cat(op(examples[exname][2])),'refresh'):
fi:
end use; 
