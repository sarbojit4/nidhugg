#!/bin/bash

tools=("optimal" "event" "lapormo" "lapor")

declare -a bench_name
declare -A trace
declare -A time
declare -A mem
for i in "${!tools[@]}"
do
    j=0
    for dir in $@
    do
	ofile=$dir/${tools[$i]}.txt
	line_no=1
	while read line
	do
	    if [ $line_no = 1 ]; then line_no=0
	    else
		col_no=0
		for col in $line
		do
		    if [ $col_no = 0 ]; then
			bench_name[$j]="\bench{"$col
		    elif [ $col_no = 1 ]; then
			bench_name[$j]=${bench_name[$j]}"("$col")}"
		    elif [ $col_no = 3 ]; then
			trace[$i,$j]=$col
		    elif [ $col_no = 4 ]; then
			time[$i,$j]=$col
		    elif [ $col_no = 5 ]; then
			if [[ "$col" =~ ^[0-9]+$ ]]; then
			   mem[$i,$j]=`echo "scale=2; $col/1024" | bc`
			else
			    mem[$i,$j]=$col
			fi
		    else
			a=$col
		    fi
		    col_no=$((col_no+1))
		done
	        j=$((j+1))
	    fi
	done < $ofile
    done
done
echo "" > all_merged.txt
for l in "${!bench_name[@]}"
do
    line=${bench_name[$l]}
    for t in "${!tools[@]}"
    do
	line=$line" & "${trace[$t,$l]}
    done
    for t in "${!tools[@]}"
    do
	line=$line" & "${time[$t,$l]}
    done
    #for t in "${!tools[@]}"
    #do
	#line=$line" & "${mem[$t,$l]}
    #done
    line=$line" \\\\"
    echo $line >> all_merged.txt
done        
