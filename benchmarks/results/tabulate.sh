#!/bin/bash

set -euo pipefail

verb=$1
shift 1

blame() {
    if grep -Eq '^real ' $1; then
        echo err
    else
        echo '{\timeout}'
    fi
}

get_traces() {
    if grep -Eq '^Error detected' $1; then
        echo -n "\bug{}"
    fi

    pat='^Number of complete executions explored: '
    if grep -Eq "$pat" $1; then
        count=$(grep -E "$pat" $1 | cut -d' ' -f6)
        if grep -Eq '^Number of blocked executions seen:' $1; then
            count="$count"+$(grep -E '^Number of blocked executions seen: ' $1 | cut -d' ' -f6)
        fi
        printf "%s\n" "$count"
    elif grep -Eq 'Fully\+partially executed traces: ' $1; then
	grep -E 'Fully\+partially executed traces: ' $1 | cut -d' ' -f5
    elif grep -Eq 'Total executions: ' $1; then
        grep -E 'Total executions: ' $1 | cut -d' ' -f3
    elif grep -Eq '^Trace count: ' $1; then
        count=$(grep -E '^Trace count: ' $1 | cut -d' ' -f3)
        bc=0
        if grep -Eq '^Assume-blocked trace count: ' $1; then
            bc=$(echo "$bc"+$(grep -E '^Assume-blocked trace count: ' $1 | cut -d' ' -f4) | bc)
        fi
        if grep -Eq '^Await-blocked trace count: ' $1; then
            bc=$(echo "$bc"+$(grep -E '^Await-blocked trace count: ' $1 | cut -d' ' -f4) | bc)
        fi
        if [ $bc -ne 0 ]; then
            count="$count"+$bc
        fi
        if grep -Eq '^Sleepset-blocked trace count: ' $1; then
            count="$count"+$(grep -E '^Sleepset-blocked trace count: ' $1 | cut -d' ' -f4)"ssb"
        fi
        printf "%s\n" "$count"
    else
        blame $1
    fi
}

get_time() {
    if grep -Eq '^real ' $1; then
        grep -E '^real ' $1 | cut -d' ' -f2
    else
        blame $1
    fi
}

get_speedup() {
    t=$(get_time $1)
    t1=$(get_time $2)
    if echo "$t" | grep -qe err -e timeout; then
        echo "$t"
    elif echo "$t1" | grep -qe err -e timeout; then
        echo "$t1"
    elif echo "$t" | grep -Eq '^0*(\.0+)?$'; then
        echo nan
    else
        printf "scale=3;%s/%s\n" "$t1" "$t" | bc
    fi
}

get_mem() {
    if grep -Eq '^res ' $1; then
        grep -E '^res ' $1 | cut -d' ' -f2
    else
        blame $1
    fi
}

case $verb in
    tool)
        bench=$1
        tool=$2
        N=$3
        shift 3
        echo -e "benchmark\tn\ttool\ttraces\ttime\tmem"
        for n in $N; do
            f="${tool}_${n}.txt"
            traces=$(get_traces "$f")
            printf "%s\t%d\t%s" $bench $n $tool
            if [ x"$traces" = xerr ]; then
                err='{\error}'
                printf "\t%s\t%s\t%s\n" "$err" "$err" "$err"
            else
                printf "\t%s\t%s\t%s\n" "$traces" $(get_time "$f") \
                       $(get_mem "$f")
            fi
        done
        ;;
    wide)
        bench=$1
        tools=$2
        N=$3
        shift 3
        echo -ne "benchmark\tn"
        for tool in $tools; do
            echo -ne "\t${tool}_traces"
        done
        for tool in $tools; do
            echo -ne "\t${tool}_time"
        done
        for tool in $tools; do
            echo -ne "\t${tool}_mem"
        done
        echo ''
        for n in $N; do
            printf "%s\t%d" $bench $n
            for tool in $tools; do
                f="${tool}_${n}.txt"
                traces=$(get_traces "$f")
                if [ x"$traces" = xerr ]; then
                    err='{\error}'
                    printf "\t%s" "$err"
                else
                    printf "\t%s" "$traces"
                fi
            done
            for tool in $tools; do
                f="${tool}_${n}.txt"
                traces=$(get_traces "$f")
                if [ x"$traces" = xerr ]; then
                    err='{\error}'
                    printf "\t%s" "$err"
                else
                    printf "\t%s" $(get_time "$f") 
                           
                fi
            done
            for tool in $tools; do
                f="${tool}_${n}.txt"
                traces=$(get_traces "$f")
                if [ x"$traces" = xerr ]; then
                    err='{\error}'
                    printf "\t%s" "$err"
                elif [ x"$traces" = x"{\timeout}" ]; then
                    tout='{\timeout}'
                    printf "\t%s" "$tout"
                else
                    res=$(get_mem $f)
                    printf "\t%d" $((res / 1024))
                fi
            done
            printf "\n"
        done
        ;;
    all_merge)
        arg=0
	for dir in $@
	do
	    ofile=$dir/wide.txt
	    line_no=1
            echo $ofile
	    while read line
	    do
		if [ $line_no = 1 ]; then line_no=0
		else
                    outline=""
		    col_no=0
		    for col in $line
		    do
			if [ $col_no = 0 ]; then
			    bench_name="\bench{"$col
			elif [ $col_no = 1 ]; then
			    outline=$outline$bench_name"("$col")}"
			else
			    outline=$outline" & "$col
			fi
		        col_no=$((col_no+1))
		    done
                    outline=$outline" \\\\"
		    echo $outline >> all_merged.txt
		fi
	    done < $ofile
	done
	;;
    *)
        echo "Unknown verb $verb" >&2
        exit 1
esac

