#!/usr/bin/env bash

for file in ../out/*.out
do
	echo $file
	./checker.exe < $file 
done

