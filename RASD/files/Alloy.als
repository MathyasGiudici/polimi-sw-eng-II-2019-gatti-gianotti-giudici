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
	smartphone: set Smartphone,
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
	payment: lone Payment,
}
{
	one payment implies accepted=True
}

//Request for group users data
sig GroupDataRequest {
	user: some StandardUser,
	specialUser: one SpecialUser,
	accepted: one Bool,
	payment: lone Payment,
}
{
	one payment implies accepted=True
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
	organizer: one StandardUser,
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
	device: set Device,
}
{
	isWorking=True implies not (batteryLevel=Empty)
	bluetoothConnection=True implies not (batteryLevel=Empty)
	batteryLevel=Empty implies bluetoothConnection=False
	batteryLevel=Empty implies isWorking=False
	isWorking=True implies (some records)
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
	isWorking=True implies not (batteryLevel=Empty)
	bluetoothConnection=True implies not (batteryLevel=Empty)
	batteryLevel=Empty implies bluetoothConnection=False
	batteryLevel=Empty implies isWorking=False
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

//Payment
sig Payment {
	amount: one Int,
	date: one Int,
}
{
	amount>=0
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

// Users can't have the same email address
fact usersCannotHaveTheSameEmailAddress
{
	no u1, u2 : StandardUser | u1.email=u2.email and u1!=u2
	no u1, u2 : SpecialUser | u1.corporateEmail=u2.corporateEmail and u1!=u2
	no u1 : StandardUser, u2 : SpecialUser | u1.email = u2.corporateEmail
}

//Bad health status implies a SOSCall within 5 seconds
fact badHealthStatusImpliesASOSCallWithin5Seconds
{
	all h : HealthStatusRecord | h.healthStatus.health=Bad
		implies (one c : SOSCall, u : StandardUser | c.date>=h.time and c.date<=h.time+5 and c in u.smartphone.sosCall)
}

//No two SOSCall in the same moment for the same user
fact noTwoSOSCallInSameMomentSameUser
{
	no c1, c2 : SOSCall, u1 : StandardUser | c1.date=c2.date and c1 in (u1.smartphone.sosCall) and c2 in (u1.smartphone.sosCall)
}

//No two or more SOSCall with same IDCAll
fact noMoreSOSCallWithSameID
{
	no c1, c2 : SOSCall | c1.callID=c2.callID and c1!=c2
}

//Only accepted single user request have a payment
fact onlyAcceptedSingleRequestHaveaPayment
{
	no s: SingleUserDataRequest | s.accepted=False
		<=> (one s.payment)
}

//Only accepted group request have a payment
fact onlyAcceptedGroupRequestHaveaPayment
{
	no s: GroupDataRequest | s.accepted=False
		<=> (one s.payment)
}

//All SOSCalls have Bad health status record (no emergency call without need)
fact allSOSCallWithABadHealthStatusRecord
{
	all  c : SOSCall, u : StandardUser | c in u.smartphone.sosCall
	implies (one h : HealthStatusRecord, u : StandardUser | h.healthStatus.health=Bad and c.date=h.time and h in u.smartphone.device.records)
}

//All group data request for less than 1000 users are not accepted
fact allGroupRequestForBigNumberUsers
{
	all r : GroupDataRequest | r.accepted=True
		implies (#r.user > 1000)
}

//Only accepted group data request can be payed
fact OnlyAcceptedGroupDataRequestCanBePayed
{
	all p : Payment, r : GroupDataRequest | p in r.payment
		implies r.accepted=True
}

//Only accepted single user request can be payed
fact OnlyAcceptedSingleUserDataRequestCanBePayed
{
	all p : Payment, r : SingleUserDataRequest | p in r.payment
		implies r.accepted=True
}

//All group data requests with more than 999 users are accepted
fact allGroupDataRequest1000UsersOrMoreAreAccepted
{
	all r : GroupDataRequest | #r.user>=1000
		implies r.accepted=True
}


// PREDICATES

//Special users can make more than one request
pred specialUsersCanMakeMoreThanOneDataRequest
{
	//some gr1, gr2 :  GroupDataRequest |  gr1.specialUser=gr2.specialUser and gr1!=gr2
	some sr1, sr2 :  SingleUserDataRequest |  sr1.specialUser=sr2.specialUser and sr1!=sr2
	//some sr :  SingleUserDataRequest, gr :  GroupDataRequest |  sr.specialUser=gr.specialUser
}

//ASSERTIONS

//No accepted group data request with less than 1000 special users
assert noLessThan1000UsersInGroupDataRequests
{
	no r : GroupDataRequest | #r.user<1000 and r.accepted=True
}

//No payment for not accepted requests
assert noPaymentForNotAcceptedSingleUserDataRequests
{
	no p : Payment, r : SingleUserDataRequest | p in r.payment and p.accepted=False
}


//No group request for 1000 users or more not accepted
assert noGroupRequestsMoreThan1000UsersNotAccepted
{
	no r : GroupDataRequest | #r.user>1000 and r.accepted=False
}

//No Bad health status with no SOSCall within 5 seconds
assert noBadHealthStatusWithNoSOSCallWithin5Seconds
{
	all h : HealthStatusRecord | h.healthStatus.health=Bad
		implies (one c : SOSCall, u : StandardUser | c.date>=h.time and c.date<=h.time+5 and c in u.smartphone.sosCall)
}


//run specialUsersCanMakeMoreThanOneDataRequest
//check noLessThan1000UsersInGroupDataRequests
//check noPaymentForNotAcceptedSingleUserDataRequests
//check noGroupRequestsMoreThan1000UsersNotAccepted
//check noBadHealthStatusWithNoSOSCallWithin5Seconds



pred show() {}

run show
