now = 0.
period = 0.

def saml.integrator (x) =
    y = ref 0.
    y := !y + x * period
    !y
end
