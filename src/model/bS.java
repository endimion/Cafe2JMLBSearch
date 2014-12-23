package model; 

public class bS {

private /*@ spec_public @*/ myArray ma = new myArray();

//@ public invariant ma.the_array != null  && 0 <= ma.the_array.length && (\typeof(ma.the_array) == \type(int[])) ;

public int the_value ;

private /*@ spec_public @*/ int the_left ; 
private /*@ spec_public @*/ int the_right ; 
private /*@ spec_public @*/ int the_pivot ; 
private /*@ spec_public @*/ boolean the_found ; 
private /*@ spec_public @*/ int the_return ;



public bS(){}

public /*@ pure @*/ myArray ar(){ return ma ;}


public /*@ pure @*/ int pivot(){return the_pivot; }
public /*@ pure @*/ int value(){return the_value;}
public /*@ pure @*/ int left(){return the_left;}
public /*@ pure @*/ int right(){return the_right;}
public /*@ pure @*/ boolean found(){return the_found ;} 
public  /*@ pure @*/ int toRetrun(){return the_return;}






	/*@ requires 
	  @         (found() == false) && 
	  @         ( ar().getIndex(pivot()) < value()) && 
	  @         ( left() != right()) &&
	  @         (pivot()  >= 0) && 
	  @         (right() >= 0) && 
	  @         (left() >= 0) ;
	  @ ensures 
	  @          (left() == \old(pivot() +1)) && 
	  @          (right() == \old(right()))   &&
	  @          (found() == (\old(ar().getIndex( (pivot() +1 + right()) / 2)))  == \old(value())) && 
	  @          (pivot() == \old( (pivot() +1 + right()) / 2) ) &&
	  @          ( (\old(ar().getIndex( (pivot() +1 + right()) / 2)))  == \old(value())  ==> 
	  @             toRetrun() == \old((pivot() +1 + right()) / 2) ) &&
	  @          ( (\old(ar().getIndex( (pivot() +1 + right()) / 2)))  != \old(value())  ==> 
	  @             toRetrun() == -1 ) ;
	*/
	public void  searchRight(){
		
		if(ma != null && the_found == false  && ar().getIndex(the_pivot) < value()
			&& left()!= right() && pivot() >= 0 && left()>=0 && right()>=0){
			
			the_left = pivot() +1;
			
			if( ar().getIndex( (pivot() +1 + right()) / 2) == value())
			{ 	the_found = true;
				the_return = (pivot() +1 + right()) / 2 ;
			}
			else{ 
				the_found = false;
				the_return = -1;
			} 
			
			the_pivot = (the_pivot + 1 + the_right) /2 ;
		}//end of requires if
	}//end of searchRight









/*@ requires (found() == false) && ( ar().getIndex(pivot()) > value()) && ( left() != right())
@ && (pivot()  >= 0) && (right() >= 0) && (left() >= 0) ;
@ ensures  (right() == \old(pivot() -1)) && (left() == \old(left())) 
@ && (found() == (\old(ar().getIndex( (pivot() -1 + left()) / 2)))  == \old(value())) 
@ && (pivot() == \old( (pivot() -1 + left()) / 2) )
@ && ( (\old(ar().getIndex( (pivot() -1 + left()) / 2)))  == \old(value())  ==> toRetrun() == \old((pivot() -1 + left()) / 2) ) 
@ && ( (\old(ar().getIndex( (pivot() -1 + left()) / 2)))  != \old(value())  ==> toRetrun() == -1 ) ; 
@*/
public void  searchLeft(){
	if ( ( the_found == false) && ( ar().getIndex(the_pivot) > the_value) && ( the_left != the_right)
			&&(ma != null)  && (the_pivot >= 0) && (the_left >= 0) && (the_right >= 0)	
	){
		the_right = the_pivot -1 ;
		
		if ( ar().getIndex((the_pivot -1 + the_left) / 2) == the_value ){
			the_found = true ;
		}else{the_found = false ;}
		
		if( ar().getIndex((the_pivot -1 + the_left) / 2) == value() ){
			the_return = (the_pivot -1 + the_left) / 2 ;
		}else{ the_return =  -1;}
		
		the_pivot = (the_pivot -1 + the_left) / 2 ;
	}
}




}



