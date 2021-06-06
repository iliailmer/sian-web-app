use DocumentTools in 

if parse(GetProperty("ComputeId", value)) then
	SetProperty("bypass", enabled, true):
	SetProperty("SkipSingle", enabled, true):
	SetProperty("SimplifiedGen", enabled, true):
	SetProperty("NoBound", enabled, true):
	SetProperty("Refine", enabled, true):


else
	SetProperty("bypass", enabled, false):
	SetProperty("SkipSingle", enabled, false):
	SetProperty("SimplifiedGen", enabled, false):
	SetProperty("NoBound", enabled, false):
	SetProperty("Refine", enabled, false):
	SetProperty("UsingUpTo", enabled, false):
	SetProperty("MaxPermutations", enabled, false):
	SetProperty("Permutations", enabled, false):

fi:
end use;