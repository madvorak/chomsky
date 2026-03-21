import Chomsky.Classes.ContextFree.ClosureProperties.Union
import Chomsky.Classes.ContextFree.ClosureProperties.Reverse
import Chomsky.Classes.ContextFree.ClosureProperties.Concatenation
-- import Chomsky.Classes.ContextFree.ClosureProperties.Intersection
-- import Chomsky.Classes.ContextFree.ClosureProperties.Complement
import Chomsky.Classes.Unrestricted.ClosureProperties.Union
import Chomsky.Classes.Unrestricted.ClosureProperties.Reverse
import Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation
import Chomsky.Classes.Unrestricted.ClosureProperties.Star
import Chomsky.Classes.ContextSensitive.Basics.Inclusion
import Chomsky.Classes.ContextSensitive.ClosureProperties.Concatenation
import Chomsky.Classes.Regular.Basics.Definition

section regular
#check IsRegular_implies_IsCF
end regular

section context_sensitive
#check IsCS_implies_IsGG
#check CS_of_CS_c_CS
end context_sensitive

section context_free
#check CF_of_CF_u_CF
#check CF_of_reverse_CF
#check CF_of_CF_c_CF
end context_free

section unrestricted
#check GG_of_GG_u_GG
#check GG_of_reverse_GG
#check GG_of_GG_c_GG
#check GG_of_star_GG
end unrestricted
