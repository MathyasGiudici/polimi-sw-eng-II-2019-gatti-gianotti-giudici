open util/boolean

//As in UNIX, time is represented as an offset in seconds from midnight (UTC) on January 1, 1970.

//String abstraction
sig StringTM {}

//SIGNATURES

//Standard user
sig StandardUser {
	email: one StringTM,
	name: one StringTM,
	surname: one StringTM,
	dateOfBirth: one Int,
	address: one Address,
	occupation: one Occupation,
}

//Special user
sig SpecialUser {
	corporateEmail: one StringTM,
	businessName: one StringTM,
	vat: one Int,
	referentsSurname: one StringTM,
	referentName: one StringTM,
	legalAddress: one Address,
	billingAddress: one Address,
	sector: one Sector,
}

//Position
sig Position {
	latitude: one Int,
	longitude: one Int,
}

//Request for single user data
sig SingleUserDataRequest {
	accepted: one Bool,
	user: one StandardUser,
	specialUser: one SpecialUser,
}

//Request for group users data
sig GroupDataRequest {
	user: some StandardUser,
	specialUser: one SpecialUser,
	accepted: one Bool,
}

//Address
sig Address {
	country: one StringTM,
	province: one StringTM,
	city: one StringTM,
	street: one StringTM,
	houseNumber: one Int,
}
{
	houseNumber>0
}

//Data of a run
sig Run {
	name: one StringTM,
	organizer: lone StandardUser,
	partecipants: set StandardUser,
	route: set Position,
}

//Smartphone
sig Smartphone {
	smartphoneID: one Int,
	bluetoothConnection: one Bool,
	isWorking: one Bool,
	batteryLevel: one BatteryLevel,
	isOnCharge: one Bool,
	records: set PositionRecord,
	sosCall: set SOSCall,
}
{
	isWorking=True implies batteryLevel!=Empty
	bluetoothConnection=True implies batteryLevel!=Empty
}

//SOSCall
sig SOSCall {
	callID: one Int,
	date: one Int,
}

//Device
sig Device {
	deviceID: one Int,
	bluetoothConnection: one Bool,
	isWorking: one Bool,
	batteryLevel: one BatteryLevel,
	isOnCharge: one Bool,
	records: set HealthStatusRecord,
}
{
	isWorking=True implies batteryLevel!=Empty
	bluetoothConnection=True implies batteryLevel!=Empty
}

//Position Record
sig PositionRecord {
	time: one Int,
	position: one Position,
}

//Health Status Record
sig HealthStatusRecord {
	time: one Int,
	healthStatus: one HealthStatus,
}

//Health Status
sig HealthStatus {
	heartbeat: one Int,
	pulsation: one Int,
	health: one Health,
}
{
	heartbeat>=0
	pulsation>=0
}

//Enum BatteryLevel
abstract sig BatteryLevel {}
	one sig Empty extends BatteryLevel{}
	one sig Low extends BatteryLevel{}
	one sig Medium extends BatteryLevel{}
	one sig High extends BatteryLevel{}

//Enum Job Sector
abstract sig Sector {}
	one sig Finance extends Sector{}
	one sig Business extends Sector{}
	one sig Pharmaceutical extends Sector{}
	one sig Engineering extends Sector{}
	one sig Environment extends Sector{}
	one sig Healthcare extends Sector{}
	one sig IT extends Sector{}
	one sig Law extends Sector{}

//Enum User Occupation
abstract sig Occupation {}
	one sig Student extends Occupation {}
	one sig Employed extends Occupation{}
	one sig Unemployed extends Occupation{}

//Enum User Health
abstract sig Health {}
	one sig Good extends Health{}
	one sig Bad extends Health{}


//FACTS




//ASSERTIONS





pred show() {}

run show for 5
