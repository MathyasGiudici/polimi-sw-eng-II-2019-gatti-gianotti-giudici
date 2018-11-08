open util/boolean

//String abstraction
sig StringTM {}

//SIGNATURES

//Standard user
sig StandardUser {
	email: one StringTM,
	name: one StringTM,
	surname: one StringTM,
	dateOfBirth: one Int,
	userPosition: lone Position,
	userAddress: one Address,
	userOccupation: some Occupation,
}

//Special user
sig SpecialUser {
	businessName: one StringTM,
	vat: one Int,
	legalAddress: one Address,
	billingAddress: one Address,
	corporateEmail: StringTM,
	sector: one Sector,
	referentName: one StringTM,
	referentsSurname: one StringTM,
}

//Position
sig Position {
	latitude: one Int,
	longitude: one Int,
}

//Request for group users data
sig GroupDataRequest {
	user: some StandardUser,
	specialUser: one SpecialUser,
	accepted: one Bool,
}

//Request for single user data
sig SingleUserDataRequest {
	user: one StandardUser,
	specialUser: one SpecialUser,
	accepted: one Bool,
}

//Address
sig Address {
	country: one StringTM,
	province: one StringTM,
	city: one StringTM,
	street: one StringTM,
	houseNumber: one Int
}
{
	houseNumber>0
}

//Route of a run
sig RunRoute {
	route: some Position,
}

//Data of a run
sig Run {
	name: one StringTM,
	route: one RunRoute,
	partecipants: set StandardUser,
	organizer: lone StandardUser,
}

//Device
sig Device {
	deviceID: one Int,
	bluetoothConnection: one Bool,
	batteryLevel: one BatteryLevel,
	isWorking: one Bool,
	isOnCharge: one Bool,
	devicePosition: one Position,
	currentMeasuredHealthStatus: lone HealthStatus
}
{
	currentMeasuredHealthStatus = Good or currentMeasuredHealthStatus = Bad implies isWorking = True
	currentMeasuredHealthStatus = Good or currentMeasuredHealthStatus = Bad implies batteryLevel != Empty
	currentMeasuredHealthStatus = Good or currentMeasuredHealthStatus = Bad implies bluetoothConnection = True
}

//Health data
sig TrackUserHealthStatus {
	user: one StandardUser,
	healthStatus: one HealthStatus,
	time: one Int,
}

//Battery level
abstract sig BatteryLevel {}
	one sig Empty extends BatteryLevel{}
	one sig Low extends BatteryLevel{}
	one sig Medium extends BatteryLevel{}
	one sig High extends BatteryLevel{}

//Job sector
abstract sig Sector {}
	one sig Finance extends Sector{}
	one sig Business extends Sector{}
	one sig Pharmaceutical extends Sector{}
	one sig Creative extends Sector{}
	one sig Energy extends Sector{}
	one sig Engineering extends Sector{}
	one sig Environment extends Sector{}
	one sig Healthcare extends Sector{}
	one sig IT extends Sector{}
	one sig Law extends Sector{}

//Job role
abstract sig Occupation {}
	one sig Student extends Occupation {}
	one sig Employed extends Occupation{}
	one sig Unemployed extends Occupation{}

//Health status
abstract sig HealthStatus {}
	one sig Good extends HealthStatus{}
	one sig Bad extends HealthStatus{}


//FACTS




//ASSERTIONS





pred show() {}

run show for 5
