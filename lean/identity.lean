theorem identityReturnsInput (x : Lynx.Term) :
    Elixir.ReductionBoundsTest.Fixture.«identity/1» x = .ok x := by
  rfl
