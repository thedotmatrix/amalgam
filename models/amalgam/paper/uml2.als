// CD2Alloy2.cd - parsed successfully!
// Alloy Model for CDs CD2Alloy2
// Generated: 2016-07-21 23:50:12 Israel Daylight Time
 
module umlp2alloy/CD2Alloy2_module

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


///////////////////////////////////////////////////
// Structures common to both CDs
///////////////////////////////////////////////////

// Concrete names of fields in cd
private one sig of extends FName {}
private one sig worksIn extends FName {}

// Concrete value types in model cd

// Concrete enum values in model cd

// Classes in model cd
sig Employee extends Obj {}
sig Address extends Obj {}
sig Driver extends Obj {}
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


pred cd {
  CD2Alloy2
}


///////////////////////////////////////////////////
// Run commands
///////////////////////////////////////////////////

run cd for 10 but 5 int 

