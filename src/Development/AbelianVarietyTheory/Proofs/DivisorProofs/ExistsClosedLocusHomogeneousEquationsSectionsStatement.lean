module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferentialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsThroughZeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomialsStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquare

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem germ_cstT_eq_germ_ringOf_C : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  intro Rg _ A₀ T X f n g φ p h z r
  have e0 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  have e1 : gs φ z ⊤ (cstT f r) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) :=
    gs_pull φ f z ⊤ trivial _
  have h1 := gs_pull (p ≫ g) (affπ Rg n) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)
  have h2 := gs_pull p g z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r))
  rw [Category.assoc] at h1
  rw [e1, h, ← h1]
  refine Eq.trans ?_ h2.symm
  change gs (p ≫ g) z ⊤ ((affπ Rg n).appTop _) = _
  rw [e0]

end GlobalTheory.FormsLocus
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.germ_constants_eq_along_affineSpace_square : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  first | (exact @GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (exact GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (intros; apply GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndep

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.formVanish_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  intro Rg _ A₀ T X N mA mB a φ p t c d F hF z q q' hq hq'
  have hV : φ z ∈ N.U q ⊓ N.U q' := ⟨hq, hq'⟩
  have hsec : ∀ i, gs φ z (N.U q) ((a i).f q) =
      (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * gs φ z (N.U q') ((a i).f q') := by
    intro i
    rw [← gs_res φ z (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q) hV, (a i).compat q q', gs_mul φ z _ hV,
      gs_unit φ z _ hV, gs_res φ z (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q') hV]
  have hcomb : comb a φ p c z q = fun j => (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    funext j
    simp only [comb, hsec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hev : ∀ (w : X.presheaf.stalk z) (y : Fin mB → X.presheaf.stalk z),
      MvPolynomial.eval₂Hom (gc (p ≫ t) z) (fun j => w * y j) F = w ^ d * MvPolynomial.eval₂Hom (gc (p ≫ t) z) y F := by
    intro w y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hd := hF (MvPolynomial.mem_support_iff.mp hm)
    have hs : ∑ i ∈ m.support, m i = d := by
      rw [← hd]; simp [Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring
  rw [hcomb, hev]
  exact IsUnit.mul_right_eq_zero ((gm φ z (N.U q ⊓ N.U q') (N.g q q')).isUnit.pow d)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndepStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  first | (exact @GlobalTheory.HomFixUniv.formVanish_chart_indep) | (exact GlobalTheory.HomFixUniv.formVanish_chart_indep) | (intros; apply GlobalTheory.HomFixUniv.formVanish_chart_indep  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixTransvectionDiagonalDecomposition

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus.VecGerm

theorem gs_map_sum {Y X : Scheme.{0}} (φ : Y ⟶ X) (z : Y) (U : X.Opens) (h : φ z ∈ U) {κ : Type} (t : Finset κ)
    (a b : κ → Γ(X, U)) : gs φ z U (∑ k ∈ t, a k * b k) = ∑ k ∈ t, gs φ z U (a k) * gs φ z U (b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq φ z U h, map_sum, map_mul]

theorem germ_eq_sum_vecOf : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  intro Rg _ A₀ X f M Q s φ z i hz
  have h := vecOf_spec Q s i
  have hz' : φ z ∈ (𝟙 A₀) ⁻¹ᵁ Q.W i := hz
  have h2 := congrArg (gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i)) h
  rw [gs_map_sum φ z _ hz'] at h2
  have hl : gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i) (GlobalTheory.AbLaw.rs A₀ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i))
      ((GlobalTheory.AbLaw.finSecPullId s).f (fun _ => Q.ch i))) = gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) := by
    unfold GlobalTheory.AbLaw.finSecPullId
    dsimp only
    exact (gs_res φ z _ hz' _).trans (gs_res φ z _ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i) hz') _)
  rw [hl] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · show gs φ z _ ((A₀.presheaf.map (homOfLE le_top).op).hom (cstT f (vecOf Q s k))) = _
    exact gs_res φ z le_top hz' _

end GlobalTheory.FormsLocus.VecGerm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalExpansion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.section_local_expansion : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  first | (exact @GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (exact GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (intros; apply GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw in
theorem germ_eq {Rg : Type} [CommRing Rg] {A₀ T X : Scheme.{0}} {f : A₀ ⟶ Sp Rg} {N : LB A₀} {mA mB : ℕ}
    (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N)
    (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T)
    (hw : φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (hF : F.IsHomogeneous d)
    (z : X) (i : (Q d).I) (hz : φ z ∈ (Q d).W i) :
    MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z ((Q d).ch i)) F =
      ∑ k, gs p z ⊤ (ringOf g (polys Q a d F k)) * gs φ z ((Q d).W i) ((Q d).u k i) := by
  have hq : φ z ∈ N.U ((Q d).ch i) := (Q d).le i hz
  have hψ : ∀ x : Γ(T, ⊤), gs p z ⊤ x =
      ((X.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom) x := fun x => gs_eq p z ⊤ trivial x
  rw [GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials Rg A₀ T X f N mA mB a g φ p hw d F hF z _ hq]
  have hv : ∀ ν, gs φ z (N.U ((Q d).ch i)) ((monSec a d ν).f ((Q d).ch i)) =
      ∑ k, gs p z ⊤ (ringOf g (MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))) * gs φ z ((Q d).W i) ((Q d).u k i) := by
    intro ν
    exact (GlobalTheory.T.section_local_expansion Rg A₀ X f _ (Q d) (monSec a d ν) φ z i hz).trans
      (Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.T.germ_constants_eq_along_affineSpace_square Rg A₀ T X f (mA * mB) g φ p hw z])

  simp only [hv, polys, hψ, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun ν _ => by ring

theorem exists_closed_formsOK : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ _ A₀ B₀ f fB N H mA mB a b hf hp hN
  have Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ)) := fun d =>
    (GlobalTheory.AbLaw.nonempty_perf_of_noetherian Rg A₀ f hf hp _ (GlobalTheory.AbLaw.isLB_pw hN d)).some
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ formIdeal Q a fB b),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formIdeal Q a fB b))),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro T X' g φ p hpb
  rw [GlobalTheory.T.factors_through_zero_locus]
  have hmem : ∀ d (z : X'), ∃ i, φ z ∈ (Q d).W i := fun d z =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [(Q d).cover]; trivial)
  constructor
  · intro hF
    have hle : formIdeal Q a fB b ≤ RingHom.ker (ringOf g) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨d, F, k, hFh, hK, rfl⟩
      have := GlobalTheory.T.eq_zero_of_differential_kernel_zero_germs Rg A₀ T X' f _ (Q d) (g ≫ affπ Rg (mA * mB)) φ p hpb
        (fun k => ringOf g (polys Q a d F k)) (GlobalTheory.T.coordinatePolynomials_form_mem_kernel_differential Rg A₀ T f N mA mB Q a g d F) (fun z i hz => by
          rw [← germ_eq Q a g φ p hpb.w d F hFh z i hz]
          exact hF d F hFh hK z ((Q d).ch i) ((Q d).le i hz))
      exact congrFun this k
    exact fun P hP => hle hP
  · intro h d F hFh hK z q hq
    obtain ⟨i, hi⟩ := hmem d z
    rw [GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep Rg A₀ T X' N mA mB a φ p _ (matOf g) d F hFh z q ((Q d).ch i) hq ((Q d).le i hi),
      germ_eq Q a g φ p hpb.w d F hFh z i hi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h _ (Ideal.subset_span ⟨d, F, k, hFh, hK, rfl⟩), gs_eq p z ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.FormsLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.FormsLocus.exists_closed_formsOK) | (exact GlobalTheory.FormsLocus.exists_closed_formsOK) | (intros; apply GlobalTheory.FormsLocus.exists_closed_formsOK <;> assumption)
end
end
