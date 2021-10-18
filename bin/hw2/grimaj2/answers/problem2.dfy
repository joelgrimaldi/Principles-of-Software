method swap(arr: array?<char>, i: int, j: int) returns (new_arr: array?<char>)
    requires arr != null
    requires 0 <= i < arr.Length
    requires 0 <= j < arr.Length
    ensures new_arr != null
    ensures new_arr.Length == arr.Length
    modifies arr
{
    var temp_char := arr[i];
    arr[i] := arr[j];
    arr[j] := temp_char;
    return arr;
}

method dutch(arr: array?<char>) returns (k: int)
    requires arr != null
    ensures k != 0 || forall i: int :: 0 <= i < k ==> arr[i] == 'r'
    ensures k != arr.Length || forall j: int :: k <= j < arr.Length ==> arr[j] == 'b'
    modifies arr
{
    k := 0;
    var counter := 0;
    while(counter < arr.Length && k < arr.Length)
        invariant 0 <= k <= arr.Length
        decreases arr.Length - counter
    {
        if(arr[counter] == 'r') { k := k+1; }
        counter := counter + 1;
    }
    var i := 0;
    if(0 < k < arr.Length){
        while(i < k && i < arr.Length)
            invariant 0 <= i <= k
            decreases k-i
        {
            if(arr[i] == 'b'){
              var j := k;
                while(j < arr.Length)
                    invariant k <= j
                    decreases arr.Length - j
                {
                    if(arr[j] == 'r'){
                        var new_arr := swap(arr,i,j);
                        arr[i] := new_arr[i];
                        arr[j] := new_arr[j];
                        break;
                    }
                    j := j+1;
                }
            }
            i := i+1;
        }
    }
    return k;
}