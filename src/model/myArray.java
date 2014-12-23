package model;



public class myArray{

private /*@ spec_public @*/ int[] the_array = new int[0];
//@ public invariant the_array != null  && 0 <= the_array.length && (\typeof(the_array) == \type(int[])) ;




public myArray(){}
	
	
public /*@ pure @*/ int getIndex(int I)
{
	if ( (I < the_array.length ) && (I >= 0 )  && (the_array != null) && (the_array[I] != 0)  ) 
		return the_array[I] ;
	else return -1 ;
}


public /*@ pure @*/ int getSize(){
	if (the_array != null)
		return the_array.length; 
	else return 0;
}





	/*@ requires (I > 0)  && (getSize() == 0) ;
	  @ ensures (getSize() == I)  &&  
	  @ (\forall int i;  getIndex(i) == \old(getIndex(i)) );
	  @
	  */
	public void setSize(int I){
		if( (I > 0) && (the_array.length == 0)   )
		the_array = new int[I];
		
	} 



	/*@ 
	  @ requires ( ( val > 0) && (getSize() > 0) && (pos < getSize()) && (pos > 0)
	  @ && (getIndex(pos -1) < val)  && ( ((pos + 1) < getSize()) && (getIndex(pos + 1) != -1)) 
	  @ && getIndex(pos +1) > val)  ;
	  @ ensures (\forall int i; (i == pos) ==> getIndex(i) == val) 
	  @ && (\forall int i; (i != pos) ==> getIndex(i) == \old(getIndex(i))) ;
	  */
	public void setIndex(int val, int pos){
		if (val > 0 && getSize() > 0 && pos < getSize() && pos >0 
				&& getIndex(pos -1) < val && pos +1 <getSize() && getIndex(pos + 1) != -1
			 && getIndex(pos +1) > val	){
			
			the_array[pos] = val;
			
		}//end of if	
	}//end of setIndex


}