#!/usr/bin/env bash

for file in ../instances/*
do
	timeout 60s ./nlsp.exe < $file > ../out/$(basename $file .inp).out
done

