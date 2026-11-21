module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  first | exact @GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue | exact GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue | (intros; apply GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue <;> assumption)
