
open declarations

// model user login

pred hasLoggedIn [t0: HTTPTransaction ] {
  some t: (t0.*cause) | t.req.path = LOGIN and some token : UserToken | token in t.req.body 
}

fact someUserCanLogin {
  some t: HTTPTransaction | t.req.path = LOGIN and some token1 : UserToken | token1 in t.req.body 
}


// model authentication token post user-login
/*
fun getAuthnId [t: HTTPTransaction]:Principal{
  {t1: (t.*cause) | isAuthenticated(t1) and none r2: (t.*cause).req| }.req.body.
}   // sugar
*/

run show {} for 6

run show {} for 3


//declarations/DNS.resolvesTo,declarations/DNS$2,declarations/NetworkEndpoint$2
