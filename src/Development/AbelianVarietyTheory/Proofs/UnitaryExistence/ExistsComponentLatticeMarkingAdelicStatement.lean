module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesStOfLandherrOfHasseNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLattice
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLatticeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') → ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧ (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  first | exact @GlobalTheory.LatticeDatum.exists_datum_of_selfDual | exact GlobalTheory.LatticeDatum.exists_datum_of_selfDual | (intros; apply GlobalTheory.LatticeDatum.exists_datum_of_selfDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometryStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  first | exact @GlobalTheory.IsoExt.exists_unitary_of_isometry | exact GlobalTheory.IsoExt.exists_unitary_of_isometry | (intros; apply GlobalTheory.IsoExt.exists_unitary_of_isometry <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.selfDual_lattice_occurs : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)) (f : ℕ → Dw.La →ₗ[𝓞 E] Λ'), l.A = 1 → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm v y) = n) ↔ v ∈ Λ') → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ v, f (n * m) a = f n a + n • v) → (∀ n : ℕ, 0 < n → (∀ a, (∃ v, f n a = n • v) ↔ ∃ v, a = n • v) ∧ ∀ a', ∃ a v, a' = f n a + n • v) → (∀ n : ℕ, 0 < n → ∀ a a', ∃ z : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm (f n a) (f n a')) - (Dw.EF a a' : ℤ) = n * z) → ∃ (k : Fin F.n) (γ : GL (Fin r) E), (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ (∀ v, v ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k).Λ) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f l.M a : Fin r → E) = (M.φ k (F.t k a) : Fin r → E) + l.M • w := by
  intro hH E _ _ _ H Dw l Xo σ' g ty F r M ξ₀ Gm φ Λ' f hA hσ hty hM hk hφ hfg hsp hsd hc hb hi
  have hξ : cc (-ξ₀) = -(-ξ₀) := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  obtain ⟨D', φ', hp, hq, hr, hφ'⟩ := GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice E H Dw r (-ξ₀) Gm φ Λ' hξ hφ hfg hsp hsd
  let e : D'.La ≃ₗ[𝓞 E] Λ' := (LinearEquiv.ofInjective φ' hφ'.1).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ x, φ' (e.symm x) = (x : Fin r → E) := fun x => by
    have : ∀ y, ((e y : Λ') : Fin r → E) = φ' y := fun y => rfl
    rw [← this, e.apply_symm_apply]
  obtain ⟨k, gam, hg1, hg2⟩ := GlobalTheory.allClassesSt_of_hasseNorm hH E H Dw l Xo σ' g ty F hA hσ hty D'
    (fun n => e.symm.toLinearMap ∘ₗ f n) hp hq
    ⟨fun n m hn hm a => by
      obtain ⟨v, hv⟩ := hc n m hn hm a
      exact ⟨e.symm v, by simp [hv]⟩,
     fun n hn => ⟨fun a => by
      rw [← (hb n hn).1 a]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [← map_nsmul, ← hv]
        simp
      · rintro ⟨v, hv⟩
        exact ⟨e.symm v, by simp [hv]⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hb n hn).2 (e a')
        refine ⟨a, e.symm v, ?_⟩
        apply e.injective
        simp [hv]⟩⟩
    (fun n hn a a' => by
      obtain ⟨z, hz⟩ := hi n hn a a'
      refine ⟨z, ?_⟩
      have h := hφ'.2.2.2.2 (e.symm (f n a)) (e.symm (f n a'))
      rw [he, he] at h
      rw [← h] at hz
      exact_mod_cast hz)
  let ψ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hψ : ∀ a, ψ a = (M.φ k a : Fin r → E) := fun a => rfl
  have hrange : Set.range ψ = ((M.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (M.φ k a).2
    · intro hv
      exact ⟨(M.φ k).symm ⟨v, hv⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨γ, hγ1, hγ2⟩ := GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry E H D' (F.Di k) r (-ξ₀) Gm φ' ψ gam hξ hφ'
    ⟨Subtype.val_injective.comp (M.φ k).injective, by rw [hrange]; exact (M.X k).Λ_span, hφ.2.2.1, hφ.2.2.2.1,
      fun x y => by
        have h := hM.ef k x y
        rw [(hk k).1, (hk k).2] at h
        exact h⟩ hg1
  refine ⟨k, γ, hγ1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun a ha => ?_⟩
  · have h := hγ2 (e.symm ⟨v, hv⟩)
    rw [he] at h
    rw [← h]
    exact (M.φ k _).2
  · have h := hγ2 (gam.symm ((M.φ k).symm ⟨_, hv⟩))
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun w => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    rw [h2, ← hr]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨w, hw⟩ := hg2 a ha
    refine ⟨M.φ k w, (M.φ k w).2, ?_⟩
    have h := hγ2 (e.symm (f l.M a))
    rw [he] at h
    rw [← h]
    change ψ (gam ((e.symm.toLinearMap ∘ₗ f l.M) a)) = ψ (F.t k a) + l.M • ψ w
    rw [hw, map_add (f := _), map_nsmul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Occ

open GlobalTheory.AdLat GlobalTheory.AdLat.Half
open scoped nonZeroDivisors

theorem form_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : FractionalIdeal (𝓞 E)⁰ E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J)
    (hg : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y) {N : ℕ} (hN : 0 < N)
    {x y x' y' : Fin n → E} (hx : x ∈ L) (hy : y ∈ L) {w w' : Fin n → RA F E}
    (hw : w ∈ hat F (L : Set (Fin n → E))) (hw' : w' ∈ hat F (L : Set (Fin n → E)))
    (ex : fv F x' = g *ᵥ (fv F x + N • w)) (ey : fv F y' = g *ᵥ (fv F y + N • w')) :
    ∃ z ∈ J, (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) = N * z := by
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  have both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)),
      hermA c G u v ∈ hat1 F (J : Set E) := fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv
  have hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x := fun x =>
    (Nat.cast_smul_eq_nsmul _ _ _).symm
  have hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N := map_natCast _ N
  have hfx := fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx
  have hfy := fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy
  have hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E) :=
    add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')
  have e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) =
      (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w') := by
    rw [ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w',
      Half.herm_smul_right, hsM]
    ring
  have e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) :=
    fun x y => hermA_tmul_fv c G 1 x y
  rw [e2, e2, ← TensorProduct.tmul_sub] at e1
  set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) :=
    (map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm
  refine ⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩
  have e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN',
    ← Algebra.TensorProduct.one_def, one_mul]
  exact hu

theorem herm_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : herm (-G) x y = -∑ a, ∑ b, x a * G a b * cc (y b) := by
  simp [herm]

theorem trace_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (hξ : cc ξ = -ξ) (x y : Fin n → E) :
    Algebra.trace ℚ E (ξ * -herm G y x) = Algebra.trace ℚ E (ξ * herm G x y) := by
  have h1 : cc (herm G x y) = herm G y x := by
    unfold herm
    unfold cc at *
    rw [Finset.sum_comm]

    simp only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)
  rw [← h2, ← h1]
  congr 1
  unfold cc at *
  change _ = IsCMField.complexConj E _
  rw [map_mul, hξ]
  ring

theorem mark_congr {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RA F E)) {N : ℕ} {x x' t w : Fin n → E} {w' : Fin n → RA F E}
    (e : A *ᵥ fv F x' = fv F (t + N • w)) (e' : fv F x' = B *ᵥ (fv F x + N • w')) :
    fv F t - (A * B) *ᵥ fv F x = N • ((A * B) *ᵥ w' - fv F w) := by
  rw [e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul] at e
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]

end GlobalTheory.Member.Occ


open GlobalTheory.Member.Occ GlobalTheory.AdLat in
theorem GlobalTheory.Member.exists_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  intro D H Dw l Xo c σ V r C hC h
  obtain ⟨hr, g, e, F, M, ι, θ, x₀⟩ := C
  subst hr
  obtain ⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩ := hC
  dsimp only at hinj hrange hisom hbase hW
  obtain ⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg1, hsp1, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨hfg, hsp, hlat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  obtain ⟨hJ, hsd1, -⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl
  obtain ⟨-, -, hsd⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1)
    (finHom V h) (latG V h) hfg1 hsp1 hlat
  let ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  have hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0 := fun k => by
    obtain ⟨h1, h2⟩ := hW k
    exact ⟨by rw [h1]; rfl, h2⟩
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg] at h
    exact neg_injective h
  have hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    rw [hisom, hT, trace_swap _ hG' _ hξ, neg_neg]
  obtain ⟨k, γ', hu, hl, hm⟩ := GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M
    (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk
    ⟨hinj, by rw [← LinearMap.coe_range, hrange]; exact hsp1, hG', by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd
    (fun n m hn hm a => hf2 n m hn hm (ε a))
    (fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans
      ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩,
        fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by
      obtain ⟨a, v, hv⟩ := (hf3 n hn).2 a'
      exact ⟨ε.symm a, v, by simpa using hv⟩⟩)
    (fun n hn a a' => by
      obtain ⟨w, hw, ew⟩ := hf1 n hn (ε a)
      obtain ⟨w', hw', ew'⟩ := hf1 n hn (ε a')
      obtain ⟨z, hz, ez⟩ := form_congr (latG V 1) (cF D) V.gramᵀ _ _
        (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'
      obtain ⟨t, ht⟩ := (hJ z).1 hz 1
      refine ⟨-t, ?_⟩
      simp only [hcc, hε] at ez
      rw [hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]
      erw [ez]
      have : -(-D.host.xi0) * -((n : D.host.E) * z) =
          (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z)) := by
        simp [Algebra.smul_def]; ring
      rw [this, map_smul, ht]
      simp)
  obtain ⟨hQ, -, hex, -, hfin⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨γ, hγ⟩ := hex γ' hu
  obtain ⟨hmv, -⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ
  obtain ⟨-, -, -, hhat1, hhat2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
    have e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hl, ← hmv]
  refine ⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨v, (hΛ v).1 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hΛ v).2 hv
  · obtain ⟨w, hw, ew⟩ := hm a ha
    obtain ⟨w', hw', ew'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)
    have m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h) := by
      rw [← SetLike.mem_coe, hhat1]
      exact ⟨w', hw', rfl⟩
    have m2 : fv D.host.F w ∈ latGHat V (γ * h) := by
      rw [hhat2]
      exact Half.fv_mem_hat' _ _ ((hΛ w).1 hw)
    refine ⟨_, sub_mem m1 m2, ?_⟩
    have e1 := (hfin γ γ' hγ).1 (f l.M (ε a))
    have ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) =
        (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w := ew
    rw [ew2] at e1
    have e2 := mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'
    rw [← Units.val_mul, ← map_mul] at e2
    exact e2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelicStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_component_lattice_marking_adelic : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  first | exact @GlobalTheory.Member.exists_mark | exact GlobalTheory.Member.exists_mark | (intros; apply GlobalTheory.Member.exists_mark <;> assumption)
end
end
