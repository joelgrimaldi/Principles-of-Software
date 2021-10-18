method product(m: int, n: int) returns(result: int)
  requires n >= 0
  ensures result == m*n
  {
    var x := m;
    var y := n;
    result := 0;
    while(y != 0)
      invariant x*y+result == m*n
      invariant y >= 0
      decreases y
      {
      if(y%2 == 0){
        double_and_halve(x, y/2);
        x := x + x;
        y := y/2;
      }
      else{
        result := result + x;
        y := y - 1;
      }
    }
    return result;
  }
  
function prod(m: int, n: int): int
  {
    m*n
  }
  
lemma double_and_halve(m:int, n:int)
  requires n >= 0
  ensures prod(m, 2 * n) == prod(m + m, n);
  {
    if (n != 0)
    {
      double_and_halve(m, n - 1);
    }
  }