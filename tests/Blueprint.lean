import ElevenTwelfths

/-! Regression checks for the exposition-facing interfaces.
Run with `lake env lean tests/Blueprint.lean` after `lake build`.
The axiom reports should contain only propext, Classical.choice and Quot.sound.
-/

open ElevenTwelfths

example (W : SmoothDyadicWeight ℂ) (X : ℕ) :
    Zeta.M W 1 X = Zeta.untwistedM W X := Zeta.M_one W X

#print axioms Zeta.S_open_square
#print axioms Zeta.M_sixth_power
#print axioms Zeta.mean_square_dyadic
#print axioms Theta.cubicSum_eq_cube_inversion
#print axioms Theta.theta_voronoi
#print axioms Theta.quadratic_large_sieve
#print axioms Zeta.densityM_bound
#print axioms riemannZeta_ne_zero_of_re_gt_elevenTwelfths
