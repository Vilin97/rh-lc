module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfF
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfA

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem expwd_core {O A E L X Y : Type*} [CommRing O] [AddCommGroup A] [Module O A]
    [AddCommGroup E] [Module O E] [AddCommGroup L] [Module O L] [AddCommGroup X] [Module O X]
    [AddCommGroup Y] [Module O Y] [Module.Flat O X]
    (j : A →ₗ[O] E) (hj : Function.Injective j) (g : L →ₗ[O] X) (μ : A ⊗[O] X →ₗ[O] Y)
    {m m' : ℕ} (a : Fin m → A) (s : Fin m → L) (b : Fin m' → A) (t : Fin m' → L)
    (h : ∑ i, j (a i) ⊗ₜ[O] s i = ∑ k, j (b k) ⊗ₜ[O] t k) :
    ∑ i, μ (a i ⊗ₜ g (s i)) = ∑ k, μ (b k ⊗ₜ g (t k)) := by
  have hinjX : Function.Injective (LinearMap.rTensor X j) :=
    Module.Flat.rTensor_preserves_injective_linearMap j hj
  have h2 := congrArg (LinearMap.lTensor E g) h

  simp only [map_sum, LinearMap.lTensor_tmul] at h2
  have h3 : LinearMap.rTensor X j (∑ i, a i ⊗ₜ[O] g (s i)) =
      LinearMap.rTensor X j (∑ k, b k ⊗ₜ[O] g (t k)) := by

    simp only [map_sum, LinearMap.rTensor_tmul]
    exact h2
  have h5 := congrArg μ (hinjX h3)

  simpa only [map_sum] using h5

theorem flat_compHom {O LL X : Type*} [CommRing O] [IsDomain O] [IsDedekindDomain O] [Field LL]
    [Algebra O LL] (hinj : Function.Injective (algebraMap O LL)) [AddCommGroup X] [Module LL X] :
    letI : Module O X := Module.compHom X (algebraMap O LL)
    Module.Flat O X := by
  letI : Module O X := Module.compHom X (algebraMap O LL)
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := hx
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have h1 : algebraMap O LL r • x = 0 := hrx
  rw [smul_eq_zero] at h1
  rw [Submodule.mem_bot]
  rcases h1 with h1 | h1
  · exact absurd ((map_eq_zero_iff _ hinj).mp h1) hr0
  · exact h1

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem lev_letE_mul (c : ZMod n) (ζ : LL) (a : LetA O n) :
    W.lev c ζ ((letE c : LetA O n) * a) = W.lev c ζ a := by
  have h0 : ((letE c : LetA O n) * a - a) c = 0 := by
    first
    | (simp [letE]; done)
    | (simp [letE, Pi.single_apply]; done)
  have h1 := W.79 c ζ _ h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

theorem levN_smul_alg (i : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T i ζ ((algebraMap O (LetA O n) o) • x) k = algebraMap O LL o • W.levN T i ζ x k := by
  rw [W.levN_smul, finsum_eq_single _ 0]
  · rw [AlgHom.commutes]
    first
    | (simp; done)
    | (simp [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]; done)
    | (simp [PowerSeries.algebraMap_apply', PowerSeries.coeff_C]; done)
    | (simp [PowerSeries.coeff_zero_eq_constantCoeff, Algebra.smul_def]; done)
  · intro j hj
    rw [AlgHom.commutes]
    first
    | (simp [hj]; done)
    | (simp [PowerSeries.algebraMap_apply, PowerSeries.coeff_C, hj]; done)
    | (simp [PowerSeries.algebraMap_apply', PowerSeries.coeff_C, hj]; done)

theorem levB_smul_alg (i : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) (k : ℤ) :
    Ct.levB T i ζ ((algebraMap O (LetA O n) o) • x) k = algebraMap O LL o • Ct.levB T i ζ x k := by
  apply framepf_ιV_inj (PD := PD) T
  rw [← Ct.levN_eq, levN_smul_alg, Ct.levN_eq, map_smul]

def val1 (c : ZMod n) (x : ↥(W.N T)) : T.V ⊗[Qp] BdR :=
  ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0))

theorem level_value_add (c : ZMod n) (x y : ↥(W.N T)) : val1 Ct T c (x + y) = val1 Ct T c x + val1 Ct T c y := by
  first
  | (simp only [val1, map_add (f := _), Pi.add_apply]; done)
  | (simp [val1]; done)
  | (simp [val1, CmpTie.levB]; done)

theorem level_value_smul (c : ZMod n) (o : O) (x : ↥(W.N T)) :
    val1 Ct T c ((algebraMap O (LetA O n) o) • x) = algebraMap O LL o • val1 Ct T c x := by
  first
  | (simp only [val1, levB_smul_alg, map_smul]; done)
  | (simp [val1, levB_smul_alg]; done)
  | (simp [val1, levB_smul_alg, map_smul]; done)

def PtHyp (c : ZMod n) (ζ : LL) : Prop :=
  IsCrys PD T.ρ ∧ (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) ∧ ζ ^ PD.p = 1 ∧
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 ∧
    (∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → W.levN T (c - 1) 1 x k = 0) ∧
    ∀ x ∈ W.N T, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T

theorem valAt_eq {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (x : ↥(W.N T)) :
    valAt W T c ζ (x : W.DD T) = val1 Ct T c x := by
  obtain ⟨hc, hζ, hζ1, hQ0, hQ1, hneg, hex⟩ := hP
  refine framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x (fun r hr => ?_) (hex _ x.2)
  apply framepf_ιV_inj (PD := PD) T
  rw [← Ct.levN_eq, hneg x r hr, map_zero]

def XO (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) : Type := T.V ⊗[Qp] BdR

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    AddCommGroup (XO BdR T) := inferInstanceAs (AddCommGroup (T.V ⊗[Qp] BdR))

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    Module LL (XO BdR T) := inferInstanceAs (Module LL (T.V ⊗[Qp] BdR))

instance (BdR : Type) [CommRing BdR] [Algebra Qp BdR] (T : LocLat G Qp LL O) :
    Module O (XO BdR T) := Module.compHom _ (algebraMap O LL)

theorem smul_XO (o : O) (x : XO BdR T) : o • x = algebraMap O LL o • x := rfl

def valL {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) :
    ↥(NcS W T (c - 1)) →ₗ[O] XO BdR T where
  toFun x := (valAt W T c ζ (x : W.DD T) : T.V ⊗[Qp] BdR)
  map_add' x y := by
    have hx : (x : W.DD T) ∈ W.N T := x.2.1.1
    have hy : (y : W.DD T) ∈ W.N T := y.2.1.1
    have e := valAt_eq Ct T hP (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [level_value_add, ← valAt_eq Ct T hP ⟨x, hx⟩, ← valAt_eq Ct T hP ⟨y, hy⟩] at e
    exact e
  map_smul' o x := by
    have hx : (x : W.DD T) ∈ W.N T := x.2.1.1
    have e := valAt_eq Ct T hP ((algebraMap O (LetA O n) o) • ⟨x, hx⟩)
    rw [level_value_smul, ← valAt_eq Ct T hP ⟨x, hx⟩] at e
    have e2 : valAt W T c ζ ((algebraMap O (LetA O n) o) • (x : W.DD T)) =
        algebraMap O LL o • valAt W T c ζ (x : W.DD T) := e
    rw [algebraMap_smul] at e2
    change valAt W T c ζ (o • (x : W.DD T)) = algebraMap O LL o • valAt W T c ζ (x : W.DD T)
    exact e2

theorem valL_ker {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0) :
    (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype ≤ LinearMap.ker (valL Ct T hP) := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 hx.1
  have hxN : (x : W.DD T) ∈ W.N T := x.2.1.1
  rw [LinearMap.mem_ker]
  change valAt W T c ζ (x : W.DD T) = 0
  rw [valAt_eq Ct T hP ⟨x, hxN⟩]
  have hzx' : (π' ^ 1) • z = (x : W.DD T) := hzx
  have hxe : (⟨x, hxN⟩ : ↥(W.N T)) = (π' ^ 1) • ⟨z, hz⟩ := by
    apply Subtype.ext
    exact hzx'.symm
  have hneg := hP.2.2.2.2.2.1
  have h0 : Ct.levB T (c - 1) 1 ⟨x, hxN⟩ 0 = 0 := by
    apply framepf_ιV_inj (PD := PD) T
    rw [← Ct.levN_eq, hxe, W.levN_smul, map_zero, pow_one]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hπ, zero_smul]
    · rw [hneg ⟨z, hz⟩ _ (by omega), smul_zero]
  simp only [val1, h0, map_zero]

def valQ {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0) : LcQ W T π' c →ₗ[O] XO BdR T :=
  Submodule.liftQ _ (valL Ct T hP) (valL_ker Ct T hP π' hπ)

def muL (c : ZMod n) (ζ : LL) : LetA O n ⊗[O] XO BdR T →ₗ[O] (ℤ → XO BdR T) :=
  TensorProduct.lift (LinearMap.mk₂ O (fun a d => serC (W.lev c ζ a) d)
    (fun a a' d => by
      funext i
      simp only [serC, map_add (f := _), Pi.add_apply]
      split_ifs <;> simp [add_smul])
    (fun o a d => by
      funext i
      simp only [serC, map_smul, Pi.smul_apply]
      split_ifs
      · rw [smul_XO, PowerSeries.coeff_smul, Algebra.smul_def, mul_smul]
      · rw [smul_zero])
    (fun a d d' => by
      funext i
      simp only [serC, Pi.add_apply]
      split_ifs <;> simp [smul_add])
    (fun o a d => by
      funext i
      simp only [serC, Pi.smul_apply]
      split_ifs
      · rw [smul_XO, smul_XO, smul_comm]
      · rw [smul_zero]))


include Ct in
theorem expS_wd [IsDomain O] [IsDedekindDomain O] (hinj : Function.Injective (algebraMap O LL))
    {c : ZMod n} {ζ : LL} (hP : PtHyp (W := W) T c ζ) (π' : LetA O n)
    (hπ : PowerSeries.constantCoeff (W.lev (c - 1) 1 π') = 0)
    {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ NcS W T (c - 1))
    (b : Fin m' → LetA O n) (z : Fin m' → W.DD T) (hz : ∀ k, z k ∈ NcS W T (c - 1))
    (h : ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k)) :
    expS W T c ζ a y = expS W T c ζ b z := by
  haveI : Module.Flat O (XO BdR T) := flat_compHom (X := XO BdR T) hinj
  have key := expwd_core (IsScalarTower.toAlgHom O (LetA O n) W.EE).toLinearMap
    (fun x y hxy => W.EE_inj hxy) (valQ Ct T hP π' hπ) (muL (W := W) T c ζ)
    (fun j => (letE c : LetA O n) * a j) (fun j => mkL W T π' c (y j) (hy j))
    (fun k => (letE c : LetA O n) * b k) (fun k => mkL W T π' c (z k) (hz k)) h
  have e1 : ∀ j, muL (W := W) T c ζ (((letE c : LetA O n) * a j) ⊗ₜ[O]
      valQ Ct T hP π' hπ (mkL W T π' c (y j) (hy j))) = serC (W.lev c ζ (a j)) (valAt W T c ζ (y j)) :=
    fun j => by
      show serC (W.lev c ζ ((letE c : LetA O n) * a j)) (valAt W T c ζ (y j)) = _
      rw [lev_letE_mul]
  have e2 : ∀ k, muL (W := W) T c ζ (((letE c : LetA O n) * b k) ⊗ₜ[O]
      valQ Ct T hP π' hπ (mkL W T π' c (z k) (hz k))) = serC (W.lev c ζ (b k)) (valAt W T c ζ (z k)) :=
    fun k => by
      show serC (W.lev c ζ ((letE c : LetA O n) * b k)) (valAt W T c ζ (z k)) = _
      rw [lev_letE_mul]
  have key2 : ∑ j, serC (W.lev c ζ (a j)) (valAt W T c ζ (y j)) =
      ∑ k, serC (W.lev c ζ (b k)) (valAt W T c ζ (z k)) := by
    refine (Finset.sum_congr rfl (fun j _ => (e1 j).symm)).trans ?_
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun k _ => e2 k))
    exact key
  funext i
  have := congrFun key2 i
  simpa [expS, Finset.sum_apply] using this

end Generic

end Formalism.MainNotions.N.Ln34.MLA

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfL

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct Formalism.MainNotions.N.Ln34.ModelFPf

theorem rec_WD (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    MLF.WD ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c := by
  intro τ ζ hpt m m' a y hy b z hz h
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hprim : IsPrimitiveRoot ζ l := framepf_pt_prim D HW hG c ζ τ hpt
  have hprim' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hp]; exact hprim
  haveI : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨-, -, -, h4W, -⟩ := hA.1 l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 letπ) = 0 := by
    rw [CrystallineExponents.cc_lev_pi ((HW l).W K 1 LL hG) (c - 1) 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hπ : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 π') = 0 := by
    obtain ⟨w, hw⟩ := hr.2.2.1
    rw [hw, map_mul, map_pow, map_mul, map_pow, hπ1, zero_pow (by omega), mul_zero]
  have hQ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hprim'
  have hP : MLA.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
    refine ⟨hT, ⟨1, by rw [pow_one]; exact hprim'⟩, hprim'.pow_eq_one, hQ.1, hQ.2, ?_, ?_⟩
    · intro x k hk
      have h4 := ((h4W T hT).1 (c - 1) 1 ⟨0, by simp⟩ (by rw [hX]; exact hπ1)).1 x k
      exact h4.2 hk
    · intro x hx
      exact ((HW l).W K 1 LL hG).N_φ T x hx
  exact MLA.expS_wd ((Cm l).C K 1 LL hG).tie T hinj hP π' hπ a y hy b z hz h


theorem exists_mul_gamma_Eat_pow_eq_Eat_pow (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) :
    ∃ u₀ ∈ ((HW l).W K 1 LL hG).AΔ, u₀ * ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK
      (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hr
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  refine ⟨((hu.unit⁻¹ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ) : LetA _ _) ^ h', Subalgebra.pow_mem _ hu'Δ h', ?_⟩
  rw [hgam, map_pow, hγ, mul_pow, ← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]


theorem rec_lev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) :
    ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK a) =
      PowerSeries.rescale (algebraMap ↥(OL LL) ↥LL.1
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hprim : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by
    rw [pow_one, hp]; exact framepf_pt_prim D HW hG c ζ τ hpt
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
    rw [hgam, Nat.cast_one (R := ↥LL.1), ((HW l).W K 1 LL hG).gam_gen, hs]
  have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 hprim hv (by rw [pow_one]) a
  exact this


theorem rec_u (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) :
    algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) :
      ↥(OL LL)) ≠ 0 ∧
    ∀ i : ℤ, i ≠ 0 → (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ
      ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL))) ^ i ≠ 1 := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have har := (framepf_hyp_arith D HW l hl K LL hG 1 hsK).1
  rw [hgam]
  set χ := ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) with hχ
  have hnat : ∀ k : ℕ, 1 ≤ k → (algebraMap ↥(OL LL) ↥LL.1 χ) ^ k ≠ 1 := by
    intro k hk h1
    have h2 : χ ^ k = 1 := by
      apply Subtype.val_injective
      have := h1
      rw [← map_pow] at this
      simpa using this
    apply har k hk
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  refine ⟨((Units.isUnit _).map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero, fun i hi h1 => ?_⟩
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · apply hnat (-i).toNat (by omega)
    have : (algebraMap ↥(OL LL) ↥LL.1 χ) ^ (-i) = 1 := by rw [zpow_neg, h1, inv_one]
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · apply hnat i.toNat (by omega)
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]

end Formalism.MainNotions.N.Ln34.MLL

end
end
end
