predicate VCalendarLeap(y: int) { y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) }
function VCalendarYearStart(y: int): int { (y-1)*365 + (y-1)/4 - (y-1)/100 + (y-1)/400 }
function VCalendarMonthLength(y: int, m: int): int
  requires 1 <= m <= 12
{ if m == 2 && VCalendarLeap(y) then 29 else [-1,31,28,31,30,31,30,31,31,30,31,30,31][m] }
function VCalendarMonthStart(y: int, m: int): int
  requires 1 <= m <= 12
{ [-1,0,31,59,90,120,151,181,212,243,273,304,334][m] + (if m > 2 && VCalendarLeap(y) then 1 else 0) }
predicate VCalendarDate(y: int, m: int, d: int) {
  y >= 1 && 1 <= m <= 12 && 1 <= d <= VCalendarMonthLength(y,m)
}
function VCalendarOrdinal(y: int, m: int, d: int): int
  requires 1 <= m <= 12
{ VCalendarYearStart(y) + VCalendarMonthStart(y,m) + d }
predicate VCalendarEncoded(y: int, m: int, d: int, n: int)
  requires 1 <= m <= 12
{ VCalendarDate(y,m,d) && n == VCalendarOrdinal(y,m,d) }
predicate VCalendarDecoded(n: int, date: (int,int,int)) {
  VCalendarDate(date.0,date.1,date.2) && VCalendarOrdinal(date.0,date.1,date.2) == n
}
lemma VCalendarYearStep(y: int)
  requires y >= 1
  ensures VCalendarYearStart(y+1) - VCalendarYearStart(y) == 365 + (if VCalendarLeap(y) then 1 else 0)
{
  assert y/4 - (y-1)/4 == (if y%4 == 0 then 1 else 0);
  assert y/100 - (y-1)/100 == (if y%100 == 0 then 1 else 0);
  assert y/400 - (y-1)/400 == (if y%400 == 0 then 1 else 0);
}
lemma VCalendarYearOrder(a: int, b: int)
  requires 1 <= a <= b
  ensures VCalendarYearStart(a) <= VCalendarYearStart(b)
{
  assert (a-1)/4 <= (b-1)/4;
  assert (a-1)/400 <= (b-1)/400;
  assert (b-1)/100 - (a-1)/100 <= b-a;
}
lemma VCalendarYearInterval(y: int, m: int, d: int)
  requires VCalendarDate(y,m,d)
  ensures VCalendarYearStart(y) < VCalendarOrdinal(y,m,d) <= VCalendarYearStart(y+1)
{
  VCalendarYearStep(y);
  assert VCalendarMonthStart(y,m) >= 0;
  assert VCalendarMonthStart(y,m) + VCalendarMonthLength(y,m) <= 365 + (if VCalendarLeap(y) then 1 else 0);
}
lemma VCalendarMonthOrder(y: int, a: int, b: int)
  requires 1 <= a < b <= 12
  ensures VCalendarMonthStart(y,a) + VCalendarMonthLength(y,a) <= VCalendarMonthStart(y,b)
{}
lemma VCalendarUnique(y: int, m: int, d: int, yy: int, mm: int, dd: int)
  requires VCalendarDate(y,m,d) && VCalendarDate(yy,mm,dd)
  requires VCalendarOrdinal(y,m,d) == VCalendarOrdinal(yy,mm,dd)
  ensures y == yy && m == mm && d == dd
{
  VCalendarYearInterval(y,m,d); VCalendarYearInterval(yy,mm,dd);
  if y < yy { VCalendarYearOrder(y+1,yy); }
  if yy < y { VCalendarYearOrder(yy+1,y); }
  assert y == yy;
  if m < mm { VCalendarMonthOrder(y,m,mm); }
  if mm < m { VCalendarMonthOrder(y,mm,m); }
  assert m == mm;
}
lemma VCalendarCycles(q: int, c: int, f: int, y: int, r: int)
  requires q >= 0 && 0 <= c <= 4 && 0 <= f <= 24 && 0 <= y <= 4 && 0 <= r < 365
  requires c*36524+f*1461+y*365+r < 146097
  requires f*1461+y*365+r < 36524
  requires y*365+r < 1461
  ensures (y == 4 || c == 4) ==> r == 0 && VCalendarDecoded(q*146097+c*36524+f*1461+y*365+r+1,(q*400+c*100+f*4+y,12,31))
  ensures (y != 4 && c != 4) ==> VCalendarYearStart(q*400+c*100+f*4+y+1) == q*146097+c*36524+f*1461+y*365
  ensures (y != 4 && c != 4) ==> VCalendarLeap(q*400+c*100+f*4+y+1) == (y == 3 && (f != 24 || c == 3))
{
  var year := q*400+c*100+f*4+y+1;
  if c == 4 {
    assert f == 0 && y == 0 && r == 0;
    assert year == (q+1)*400+1;
    assert VCalendarYearStart(year) == (q+1)*146097;
    VCalendarYearStep(year-1);
  } else if y == 4 {
    assert r == 0 && f < 24;
    assert (year-1)/4 == q*100+c*25+f+1;
    assert (year-1)/100 == q*4+c;
    assert (year-1)/400 == q;
    VCalendarYearStep(year-1);
  } else {
    assert (year-1)/4 == q*100+c*25+f;
    assert (year-1)/100 == q*4+c;
    assert (year-1)/400 == q;
    assert year%4 == (y+1)%4;
    assert year%100 == (f*4+y+1)%100;
    assert year%400 == (c*100+f*4+y+1)%400;
  }
}
