use DocumentTools in 
if parse(GetProperty("RunSIAN", value)) then

	SetProperty("printSolutions", enabled, true):
	SetProperty("bypass", enabled, true):
	SetProperty("p", enabled, true):
	SetProperty("params", enabled, true):
	SetProperty("replicas", enabled, true):
else
	SetProperty("bypass", enabled, false):
	SetProperty("printSolutions", enabled, false):
	SetProperty("p", enabled, false):
	SetProperty("params", enabled, false):
	SetProperty("replicas", enabled, false):
fi:
end use; 
