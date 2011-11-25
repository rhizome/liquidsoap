now = 0.
period = 0.

saml.period = 0.

def saml.integrator_simple (x) =
    y = ref 0.
    y := !y + x * period
    !y
end
