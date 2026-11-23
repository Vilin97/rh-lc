module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHOfIsFrob
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtDAlgebraMapPowCharMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobLiftPsiNatCastMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsGeneratedDlog
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularFunctionsPthPowerTwist
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegrality

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedFrobLogForm

section

@[expose] public section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGamma

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

namespace FrobTwist

def Tw (K V : Type) [CommRing K] [AddCommGroup V] [Module K V] : Type := ExteriorAlgebra K V

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

instance : Ring (Tw K V) := inferInstanceAs (Ring (ExteriorAlgebra K V))

abbrev twAlg (p : ℕ) [Fact p.Prime] [CharP K p] : Algebra K (Tw K V) :=
  RingHom.toAlgebra' ((algebraMap K (ExteriorAlgebra K V)).comp (frobenius K p))
    (fun c x => Algebra.commutes (R := K) (A := ExteriorAlgebra K V) _ x)

end FrobTwist


open FrobTwist in
theorem exists_isGamma {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (f : V →+ V) (hf : ∀ (c : K) v, f (c • v) = c ^ p • f v) :
    ∃ γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V, IsGamma p f γ := by
  letI : Algebra K (Tw K V) := twAlg p
  let g : V →ₗ[K] Tw K V :=
    { toFun := fun v => (ExteriorAlgebra.ι K (f v) : ExteriorAlgebra K V)
      map_add' := fun v w => by
        show ExteriorAlgebra.ι K (f (v + w)) = ExteriorAlgebra.ι K (f v) + ExteriorAlgebra.ι K (f w)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        have h1 : ExteriorAlgebra.ι K (f (c • v)) =
            algebraMap K (ExteriorAlgebra K V) (c ^ p) * ExteriorAlgebra.ι K (f v) := by
          rw [hf, map_smul, Algebra.smul_def]
        exact h1 }
  have hg : ∀ v, g v * g v = 0 := fun v => ExteriorAlgebra.ι_sq_zero (R := K) (f v)
  let Γ : ExteriorAlgebra K V →ₐ[K] Tw K V := ExteriorAlgebra.lift K ⟨g, hg⟩
  refine ⟨(Γ.toRingHom : ExteriorAlgebra K V →+* ExteriorAlgebra K V), ?_, ?_⟩
  · intro c
    have := Γ.commutes c
    exact this
  · intro v
    have := ExteriorAlgebra.lift_ι_apply K (A := Tw K V) g hg v
    exact this

end GlobalTheory.DI
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExteriorDerivativeIsDifferential

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exterior_derivative_is_differential : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  first | exact @_root_.GlobalTheory.LogDR.isExtD_extD | exact _root_.GlobalTheory.LogDR.isExtD_extD | (intros; apply _root_.GlobalTheory.LogDR.isExtD_extD <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsGeneratedDlog

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.log_forms_generated_dlog : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X), (∀ w ∈ locRing y, ExteriorAlgebra.ι X.functionField (dK w) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1) ∧ ∀ g, LogUnit Z y g → ExteriorAlgebra.ι X.functionField (dlog g) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1 := by
  first | exact @_root_.GlobalTheory.DI.dK_dlog_mem_forms_one | exact _root_.GlobalTheory.DI.dK_dlog_mem_forms_one | (intros; apply _root_.GlobalTheory.DI.dK_dlog_mem_forms_one <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegralityStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.splitting_local_integrality : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  first | exact @_root_.GlobalTheory.DI.decomp_pointwise | exact _root_.GlobalTheory.DI.decomp_pointwise | (intros; apply _root_.GlobalTheory.DI.decomp_pointwise <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem mem_latSec_iff {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens)
    (v : V) : v ∈ latSec M U ↔ ∀ y ∈ U, v ∈ M y := by
  simp only [latSec, AddSubgroup.mem_iInf]

theorem latSec_anti {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) {U U' : X.Opens}
    (h : U' ≤ U) : latSec M U ≤ latSec M U' := fun v hv =>
  (mem_latSec_iff M U' v).2 fun y hy => (mem_latSec_iff M U v).1 hv y (h hy)

theorem forms_le_of_subset_of_subset {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {B B' : Set K}
    {L L' : Set V} (q : ℕ) (hB : B ⊆ B') (hL : L ⊆ L') : forms B L q ≤ forms B' L' q :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, hB hb, v, fun k => hL (hv k), e⟩

theorem f_dlog_of_frob {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (hf : IsF p π F f) (g : Kˣ) (z : Kt)
    (hz : π z = g) (hF : F z = z ^ p) : f (dlog g) = dlog g := by
  have key := hf.2 z 0 (by rw [hF]; ring)
  rw [map_zero, map_zero, add_zero, hz] at key
  have hp := (Fact.out : p.Prime)
  have e1 : ((g : K)⁻¹) ^ p * (g : K) ^ (p - 1) = (g : K)⁻¹ := by
    have hg : (g : K) ≠ 0 := g.ne_zero
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm ((g : K)⁻¹ ^ n), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hg, one_pow, mul_one]
  simp only [dlog, dK, Units.val_inv_eq_inv_val]
  rw [hf.1, key, smul_smul, e1]

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem decomp_of_isLifted : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  intro p _ X _ _ Z ι _ U n x W G H hnp hgen hcoord hW hlift hEff hdT hCart a b hHyp
  obtain ⟨Kt, _, π, F, hπ, hF, hz, hlog⟩ := hlift
  choose f hf using fun i => exists_isF_of_flatLift p π (F i) hπ (hF i)
  choose h hh using fun i j => exists_isH_of_isFrob p π (F i) (F j) hπ (hF i) (hF j)
  have hd := GlobalTheory.T.exterior_derivative_is_differential X.functionField
  have hdat := isDatum_of_frobenius_lifts p π F (extD X.functionField) f h hπ hF hd hf hh
  choose γ hγ using fun i => exists_isGamma p (f i) (hf i).1

  have hWmono : ∀ s t : Finset ι, s.Nonempty → s ⊆ t → W t ≤ W s := by
    intro s t hs hst y hy
    exact (hW s hs y).2 fun i hi => (hW t (hs.mono hst) y).1 hy i (hst hi)
  have hgenW : ∀ s : Finset ι, s.Nonempty → genericPoint X ∈ W s := fun s hs =>
    (hW s hs _).2 fun i _ => hgen i
  have hNuniv : ∀ a' (s : Finset ι), s.Nonempty →
      logSec Z G a' (W s) ≤ forms (Set.univ : Set X.functionField) (Set.univ : Set Ω[X.functionField⁄ℤ]) a' := by
    intro a' s hs v hv
    have := (mem_latSec_iff _ _ v).1 hv _ (hgenW s hs)
    exact forms_le_of_subset_of_subset a' (Set.subset_univ _) (Set.subset_univ _) this
  refine GlobalTheory.T.splitting_local_integrality (K := X.functionField) (V := Ω[X.functionField⁄ℤ]) p (extD X.functionField) f h γ
    (P := X) (fun s => {y | ∀ i ∈ s, y ∈ U i}) (fun y => locRing y) (fun y => {c | G.RegularAt y c})
    (fun y => dlog '' {g | LogUnit Z y g}) (fun q s => logSec Z G q (W s)) (fun q s => logSec Z H q (W s))
    hd.toIsOddDer hdat hγ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b hHyp
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s v hv
    exact hdT q s v hv
  · intro a' s hs
    exact hNuniv a' s hs
  · intro a' s hs hpa
    obtain ⟨i, -⟩ := id hs
    rw [eq_bot_iff]
    refine (hNuniv a' s hs).trans (le_of_eq ?_)
    exact spanForms_eq_bot_of_lt_card X.functionField n (x i) _ _ a' (hcoord i) (by omega)
  · intro a' s hs y hy v hv
    exact (mem_latSec_iff _ _ v).1 hv y ((hW s hs y).2 hy)
  · intro q s v hs _ hv
    refine (mem_latSec_iff _ _ v).2 fun y hy => ?_
    exact forms_le_of_subset_of_subset q (GlobalTheory.T.regular_functions_pth_power_twist p G H y hEff) subset_rfl (hv y ((hW s hs y).1 hy))
  · rintro s y hy i hi _ ⟨g, hg, rfl⟩
    obtain ⟨hfi, -⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    obtain ⟨w, hwA, hw⟩ := hfi i hi
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e, hw g.ne_zero, map_add (f := _), ← e]
    exact AddSubgroup.add_mem _ ((GlobalTheory.T.log_forms_generated_dlog Z y).2 g hg) ((GlobalTheory.T.log_forms_generated_dlog Z y).1 w hwA)
  · rintro s y hy i hi j hj _ ⟨g, hg, rfl⟩
    obtain ⟨-, hhij⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e]
    exact hhij i hi j hj
  · intro s j hj
    refine hCart s j hj (γ j) ⟨(hγ j).1, fun l => ?_⟩
    obtain ⟨z, hzx, hzF⟩ := hz j l
    rw [(hγ j).2, f_dlog_of_frob p π (F j) (f j) (hf j) (x j l) z hzx hzF]

end GlobalTheory.DI
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLiftStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.cech_log_forms_frobenius_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  first | exact @_root_.GlobalTheory.DI.decomp_of_isLifted | exact _root_.GlobalTheory.DI.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.DI.decomp_of_isLifted <;> assumption)
end
end
