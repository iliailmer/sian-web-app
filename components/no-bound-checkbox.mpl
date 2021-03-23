use DocumentTools in 
	if parse(GetProperty("Refine", value)) then
		SetProperty("Refine", value, false):
		SetProperty("UsingUpTo", enabled, false):
		SetProperty("MaxPermutations", enabled, false):
		SetProperty("Permutations", enabled, false):
	fi:
end use; 
