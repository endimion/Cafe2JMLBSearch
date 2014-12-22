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
  @*/
public void setSize(int I){
	if( (I > 0) && (the_array.length == 0)   )
	the_array = new int[I];
	
}



/*@ requires (I1 > 0) && (getSize() > 0) && (I2 < getSize()) && (I2 > 0)
  @ && (getIndex(A,I2 -1) < I1) 
  @ && ( ((I2 + 1) < getSize(A)) && (getIndex(A,I2 + 1) != -1) ==> getIndex(A,I2 +1) > I1)  
  @  ;
  @ ensures (\forall int i; (i == I2) ==> getIndex(i) == I1) 
  @ && (\forall int i; (i != I2) ==> getIndex(i) == \old(getIndex(i))) ;
  @ also 
  @ requires !((I1 > 0) && (getSize() > 0) && (I2 < getSize()) && (I2 > 0)
  @ && (getIndex(A,I2 -1) < I1) && ( ((I2 + 1) < getSize(A)) ==> getIndex(A,I2 +1) > I1  ))  ;
  @ assignable \nothing ;
  @  
 */
public void setIndex(int I1, int I2){
	if ((I2 < this.getSize() ) && (this.getSize() > 0 ) && (I1 > 0) && (I2 > 0)) 
	{	if( getIndex(I2 -1) < I1) 
			if( (I2 +1 < getSize()) && (getIndex(I2 +1) != -1)){
				if( getIndex(I2+1) > I1) the_array[I2] = I1 ;
			}else the_array[I2] = I1;
	}
		
	 
	
}


}