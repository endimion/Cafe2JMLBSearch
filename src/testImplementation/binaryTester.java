package testImplementation;

import model.bS;


public class binaryTester {

//private static myArray the_array = new myArray();
private static bS binarySearch = new bS() ;




public static void main(String args[]){


	
	binarySearch.ar().setIndex(3,0);
	binarySearch.ar().setIndex(7,1);
	binarySearch.ar().setIndex(9,2);
	binarySearch.ar().setIndex(10,3);
	binarySearch.ar().setIndex(10,4);
	binarySearch.ar().setIndex(11,5);
	binarySearch.ar().setIndex(12,6);
	binarySearch.ar().setIndex(13,7);
	binarySearch.ar().setIndex(10,8);
	
	binarySearch.the_value = 10 ;
	
	while(true){
		binarySearch.searchLeft();
		binarySearch.searchRight();
		System.out.println(binarySearch.toRetrun());
		if(binarySearch.found()){
			System.out.println("the key is at " + binarySearch.toRetrun() );
			break;
		}
		
		
		
		
	}
	
	
}








}
