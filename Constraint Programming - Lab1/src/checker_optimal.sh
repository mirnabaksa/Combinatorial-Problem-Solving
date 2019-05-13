#!/usr/bin/env bash

input="../results.txt"
while IFS="	" read -r file depth size
do
	output="../out/$(basename $file .inp).out"
	
	if [ -f $output ]; then
	
		n=$(sed -n '1p' $output | tr -d '\n')
		index=$((2**$n+2))
	
		line=$(sed -n "$index p" $output | tr -d '\n')
		IFS=" " read d s <<< $line
	
		if [ $depth = $d -a $size = $s ]; then 
			echo "OK!"
		else
			echo $output " solution not optimal!"
		fi
	
	else
		echo $output " solution not found!"
	fi
	
done < "$input"
