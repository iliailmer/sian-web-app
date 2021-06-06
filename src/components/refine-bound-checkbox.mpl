use DocumentTools in 
	if parse(GetProperty("NoBound", value)) then
		SetProperty("NoBound", value, false):
	fi:
	if parse(GetProperty("Refine", value)) then
		
		SetProperty("UsingUpTo", enabled, true):
		SetProperty("MaxPermutations", enabled, true):
		SetProperty("Permutations", enabled, true):
	else
		SetProperty("UsingUpTo", enabled, false):
		SetProperty("MaxPermutations", enabled, false):
		SetProperty("Permutations", enabled, false):
	fi:
end use; 
