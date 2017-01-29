public class IntervalDriver {

  // Do not change or add annotations in this class!
  //@ public invariant this != null;
  
  /*@ requires i1 != null;
    @ requires i2 != null;
    @ ensures \result != null;
    @ ensures \result.low == \result.high
    @         || (\result.low == Math.min(i1.low, i2.low) 
    @         && \result.high == Math.max(i1.high, i2.high));
    @*/
  OpenInterval joinIntervals(OpenInterval i1, OpenInterval i2) {
    // Returns empty interval if i1 and i2 are non-overlapping.
    if (i1.getHigh() <= i2.getLow() || i2.getHigh() <= i1.getLow()) {
        return new OpenInterval(0);
    }

  // Joins i1 and i2.
  int low = i1.getLow() < i2.getLow() ? i1.getLow() : i2.getLow();
	int high = i1.getHigh() > i2.getHigh() ? i1.getHigh() : i2.getHigh();
    return new OpenInterval(low, high);
  }

}

class OpenInterval{

    // Do not change implementations in this class!
    private /*@ spec_public @*/ int low;
    private /*@ spec_public @*/ int high;

    // Do not change this invariant!
    //@ invariant low <= high;

	/*@ requires low <= high;
    @ assignable this.low, this.high;
    @ ensures this.low == low && this.high == high;
	  @*/
    public OpenInterval(int low, int high){
	this.low = low;
	this.high = high;
    }

	// 
	/*@ assignable this.low, this.high;
    @ ensures this.low == x && this.high == x;
    @ ensures this.low == this.high;
	  @*/
    // Creates an empty interval.
    public OpenInterval(int x){
	this.low = x;
	this.high = x;
    }	
     
	 
	  //@ ensures \result == this.low;
    public /*@ pure @*/ int getLow(){
	return this.low;
    }

    //@ ensures \result == this.high;
    public /*@ pure @*/ int getHigh(){
	return this.high;
    }

    /*@ requires x != null;
      @ ensures \result == (this.low == x.low && this.high == x.high);
      @*/
    public /*@ pure */ boolean equals(OpenInterval x){
	return (this.low == x.low && this.high == x.high);
    }
    

}

