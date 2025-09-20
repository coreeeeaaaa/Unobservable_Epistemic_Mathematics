namespace UEM
structure Token where sym : String
def combine (a b : Token) : Token := ⟨a.sym ++ b.sym⟩
end UEM