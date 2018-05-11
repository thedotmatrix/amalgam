/*
	Structure:
		- generic defns 
		- m1 defns
		- m2 defns (minus field defns etc. used by m1, too)
		- diff preds

	Created manually by TN since we don't get the .als
	model created by CDDiff directly; started from CD2Alloy.
*/

////////////////////////////////////////////////////////

///////////////////////////////////////////////////
// Generic Head of CD Model - Apr. 28, 2011
///////////////////////////////////////////////////

//Names of fields/associations in classes of the model
private abstract sig FName {}

//Names of enum values in enums of the model
private abstract sig EnumVal {}

//Values of fields
private abstract sig Val {}

//Parent of all classes relating fields and values
abstract sig Obj {
	get : FName -> { Obj + Val + EnumVal }
}

pred ObjFNames[objs: set Obj, fNames:set  FName] {
	no objs.get[FName - fNames]
}

pred ObjAttrib[objs: set Obj, fName:one FName, fType: set { Obj + Val + EnumVal }] {
	objs.get[fName] in fType
	all o: objs | one o.get[fName]
}

pred ObjMeth[objs: set Obj, fName: one FName, fType: set { Obj + Val + EnumVal }] {
	objs.get[fName] in fType	
	all o: objs | one o.get[fName]
}

pred ObjLUAttrib[objs: set Obj, fName:one FName, fType: set Obj, low: Int, up: Int] {
	ObjLAttrib[objs, fName, fType, low]
	ObjUAttrib[objs, fName, fType, up]
}

pred ObjLAttrib[objs: set Obj, fName:one FName, fType: set Obj, low: Int] {
	objs.get[fName] in fType
	all o: objs | (#o.get[fName] >= low)  
}

pred ObjUAttrib[objs: set Obj, fName:one FName, fType: set Obj, up: Int] {
	objs.get[fName] in fType
	all o: objs | (#o.get[fName] =< up)
}

pred ObjLU[objs: set Obj, fName:one FName, fType: set Obj, low: Int, up: Int] {
	ObjL[objs, fName, fType, low]
	ObjU[objs, fName, fType, up]
}

pred ObjL[objs: set Obj, fName:one FName, fType: set Obj, low: Int] {
	all r: objs | # { l: fType | r in l.get[fName]} >= low
}

pred ObjU[objs: set Obj, fName:one FName, fType: set Obj, up: Int] {
	all r: objs | # { l: fType | r in l.get[fName]} =< up
}

pred BidiAssoc[left: set Obj, lFName:one FName, right: set Obj, rFName:one FName] {
	all l: left | all r: l.get[lFName] | l in r.get[rFName]
	all r: right | all l: r.get[rFName] | r in l.get[lFName]
}

pred Composition[compos: Obj->Obj, right: set Obj] {
	all r: right | lone compos.r
}

fun rel[wholes: set Obj, fn: FName]  : Obj->Obj {
  {o1:Obj,o2:Obj | o1->fn->o2 in wholes <: get}
}

fact NonEmptyInstancesOnly {
  some Obj
}

////////////////////////////////////////////////////////

// Concrete names of fields in cd
private one sig color extends FName {}
private one sig drives extends FName {}
private one sig of extends FName {}
private one sig drivenBy extends FName {}
private one sig worksIn extends FName {}

// Concrete value types in model cd

// Concrete enum values in model cd
private one sig enum_ColorKind_red extends EnumVal {}
private one sig enum_ColorKind_black extends EnumVal {}
private one sig enum_ColorKind_white extends EnumVal {}

// Classes in model cd
sig Employee extends Obj {}
sig Address extends Obj {}
sig Car extends Obj {}
sig Driver extends Obj {}

// Interfaces in model cd

///////////////////////////////////////////////////
// CD CD2Alloy1
///////////////////////////////////////////////////

// Types wrapping subtypes
fun EmployeeSubsCDCD2Alloy1: set Obj  {
    Employee + Driver 
} 
fun AddressSubsCDCD2Alloy1: set Obj  {
    Address 
} 
fun CarSubsCDCD2Alloy1: set Obj  {
    Car 
} 
fun DriverSubsCDCD2Alloy1: set Obj  {
    Driver 
} 

// Types containing subtypes for definition of associations

// Relations that represent compositions which the class is a part of

// Enums
// Enum values in cd
fun ColorKindEnumCDCD2Alloy1: set EnumVal  {
    enum_ColorKind_red + enum_ColorKind_black + enum_ColorKind_white 
} 


// Values and relations in cd
pred CD2Alloy1 {

  // Definition of class Employee
  ObjFNames[Employee,  worksIn +  none]
  // Definition of class Address
  ObjFNames[Address,  none]
  // Definition of class Car
  ObjAttrib[Car, color, ColorKindEnumCDCD2Alloy1]
  ObjFNames[Car,  color +  drivenBy +  none]
  // Definition of class Driver
  ObjFNames[Driver,  drives +  worksIn +  none]
    
  // Special properties of singletons, abstract classes and interfaces

  // Associations
  ObjLUAttrib[EmployeeSubsCDCD2Alloy1, worksIn, AddressSubsCDCD2Alloy1, 1, 3]
  ObjLU[AddressSubsCDCD2Alloy1, worksIn, EmployeeSubsCDCD2Alloy1, 1, 1]
 	BidiAssoc[DriverSubsCDCD2Alloy1, drives, CarSubsCDCD2Alloy1, drivenBy]
  ObjLUAttrib[CarSubsCDCD2Alloy1, drivenBy, DriverSubsCDCD2Alloy1, 1, 1]
  ObjLUAttrib[DriverSubsCDCD2Alloy1, drives, CarSubsCDCD2Alloy1, 0, 1]

	// Compositions

  
  
  Obj = (Employee + Address + Car + Driver)
}


////////////////////////////////////////////////////////


// Concrete names of fields in cd
// DUPE // private one sig of extends FName {}
// DUPE // private one sig worksIn extends FName {}

// Concrete value types in model cd

// Concrete enum values in model cd

// Classes in model cd
// DUPE // sig Employee extends Obj {}
// DUPE // sig Address extends Obj {}
// DUPE // sig Driver extends Obj {}
sig Manager extends Obj {}

// Interfaces in model cd

///////////////////////////////////////////////////
// CD CD2Alloy2
///////////////////////////////////////////////////

// Types wrapping subtypes
fun EmployeeSubsCDCD2Alloy2: set Obj  {
    Employee + Driver + Manager 
} 
fun AddressSubsCDCD2Alloy2: set Obj  {
    Address 
} 
fun DriverSubsCDCD2Alloy2: set Obj  {
    Driver 
} 
fun ManagerSubsCDCD2Alloy2: set Obj  {
    Manager 
} 

// Types containing subtypes for definition of associations

// Relations that represent compositions which the class is a part of

// Enums
// Enum values in cd

// Values and relations in cd
pred CD2Alloy2 {

  // Definition of class Employee
  ObjFNames[Employee,  worksIn +  none]
  // Definition of class Address
  ObjFNames[Address,  none]
  // Definition of class Driver
  ObjFNames[Driver,  worksIn +  none]
  // Definition of class Manager
  ObjFNames[Manager,  worksIn +  none]
    
  // Special properties of singletons, abstract classes and interfaces

  // Associations
  ObjLUAttrib[EmployeeSubsCDCD2Alloy2, worksIn, AddressSubsCDCD2Alloy2, 1, 1]
  ObjLU[AddressSubsCDCD2Alloy2, worksIn, EmployeeSubsCDCD2Alloy2, 1, 1]

	// Compositions

  
  
  Obj = (Employee + Address + Driver + Manager)
}


////////////////////////////////////////////////////////

//run CD2Alloy1 for 10 but 5 int 
run CD2Alloy2 for 10 but 5 int 

/*
	M1 (CD2Alloy1) has 
		- cars, each of which is colored
		- drivenby/drives
		- 1..3 addresses per employee
	M2 (CD2Alloy2) has
		- no cars, but has managers
		- 1 address per employee

	So M1 - M2 should contain
		- instances involving a car
		- instances involving (possibly) no car but >1 addr
	M2 - M1 should contain
		- instances involving a manager
*/

// Reduced bounds from 10 so that we could cut/paste
// into Java more easily (10 was too big for a method)

pred m1_minus_m2 {
	CD2Alloy1 and not CD2Alloy2
}
run m1_minus_m2 for 6 but 5 int 

pred m2_minus_m1 {
	CD2Alloy2 and not CD2Alloy1
}
//run m2_minus_m1 for 6 but 5 int 

