module

public import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace
public import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleThirdOfSecondEleventh
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
public import Formalism.LocalToGlobal.InertKernelTheory.SclY
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K1RepresentativesLTOfDictionary
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDict
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgebraicTranslatesAllData

section

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

namespace AlgTP

open NumberField Formalism.BasicNotions Formalism.L2.Ker

theorem exists_inert_prime (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (n : ℕ) :
    ∃ p, n < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = -1 := by
  have : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  have hu : IsUnit (-1 : ZMod (4 * d)) := isUnit_one.neg
  obtain ⟨p, hpn, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu n
  refine ⟨p, hpn, hp, ?_⟩
  have hmod : (p : ℤ) ≡ -1 [ZMOD ((4 * d : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hpa
  have hm4 : (p : ℤ) ≡ -1 [ZMOD 4] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_right _ h
  have hmd : (p : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
    have h : (p : ℤ) ≡ -1 [ZMOD 4 * (d : ℤ)] := by simpa using hmod
    exact Int.ModEq.of_mul_left _ h
  have hp4 : p % 4 = 3 := by
    unfold Int.ModEq at hm4
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  have hdodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_three_mod_four hp4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, jacobiSym.mod_left' hmd,
    jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd4]
  norm_num

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ w := by
  rw [Submodule.mem_one]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (w : E) :
    w ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ w := by
  rw [RingHom.mem_range]
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).symm

theorem exists_den (D : D7) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ s : ℕ, 0 < s ∧ (∀ x ∈ L, (s : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N) ∧
      ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N, (s : D.host.E) • x ∈ L := by
  let _ := D.host.cmStar
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun v => Finset.univ.image v)
  have hint : ∀ w ∈ S.biUnion (fun v => Finset.univ.image v), IsIntegral ℤ ((y.natAbs : D.host.E) * w) := by
    intro w hw
    have h := hy w hw
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℤ) : D.host.E) = (y : D.host.E) := by rw [← e]
      rw [← this] at h
      simpa using h
    · have : ((y.natAbs : ℤ) : D.host.E) = -(y : D.host.E) := by
        rw [show ((y.natAbs : ℤ)) = -y by omega]; push_cast; ring
      have h' := h.neg
      rw [show -((y : D.host.E) * w) = ((y.natAbs : ℤ) : D.host.E) * w by rw [this]; ring] at h'
      simpa using h'
  have hfirst : ∀ x ∈ L, ((y.natAbs : ℕ) : D.host.E) • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
    have hgen : ∀ v ∈ (S : Set (Fin N → D.host.E)), ((y.natAbs : ℕ) : D.host.E) • v ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro v hv
      rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi]
      intro i _
      rw [mem_one_iff, Pi.smul_apply, smul_eq_mul]
      exact hint (v i) (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, hfirst, ?_⟩
  intro x hx
  refine (hL.2.2 _).2 ?_
  intro z hz
  have hz' := hfirst z hz
  rw [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi] at hx hz'
  have e : stdH D.host.E N z (((y.natAbs : ℕ) : D.host.E) • x) =
      stdH D.host.E N (((y.natAbs : ℕ) : D.host.E) • z) x := by
    unfold stdH
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast]
    ring
  rw [e, mem_range_iff]
  unfold stdH
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
  · have h := (mem_one_iff _).1 (hz' i (Set.mem_univ i))
    have h2 := h.map (starRingEnd D.host.E).toIntAlgHom
    convert h2 using 1 <;> rfl
  · exact (mem_one_iff _).1 (hx i (Set.mem_univ i))

theorem algebraic_translates_all_data : AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ⟨a, ha, hat⟩ α
  obtain ⟨s, hs, hsL1, hsL2⟩ := exists_den D L hA.2.2.1
  obtain ⟨s', hs', hsL1', hsL2'⟩ := exists_den D L' hA.2.2.2
  have hd := D.host.hyp
  obtain ⟨p, hpn, hp, hJ⟩ :=
    exists_inert_prime D.host.d hd.2.1 (by have := hd.2.2.2.1; omega) (a * s * s' + 4)
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < a * s * s' := by positivity
  have hcop : ∀ m : ℕ, m ∣ a * s * s' → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      absurd (Nat.le_of_dvd hpos (h.trans hm)) (by omega))
  have H := (AlgP.algebraic_fact_kernels D cc δ B hcc hδ χ hχ p (by omega) hJ N N').1 L L' hA
    ⟨s, hcop s (Dvd.intro_left _ rfl |>.mul_right _), hsL2, hsL1⟩
    ⟨s', hcop s' (Dvd.intro_left _ rfl), hsL2', hsL1'⟩ t
    ⟨a, ha, hcop a ((Dvd.intro _ rfl).mul_right _), hat⟩
  exact H.2 α

theorem algT_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ}
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.AlgT χ :=
  algebraic_translates_all_data D cc δ B χ hcc hδ hχ

end AlgTP

end Formalism.L2.KerInert
end
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelLawGlobal

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

theorem linSub_scl {σ R : Type} [Fintype σ] [CommRing R] (c : R) (A : σ → σ → R) (G : MvPowerSeries σ R) :
    Formalism.MainNotions.FormalGroupSystem.linSub (fun x y => c * A x y) G = Formalism.MainNotions.FormalGroupSystem.linSub A (Formalism.L2.KerInert.Rep.sclY c G) := by
  have ha : MvPowerSeries.HasSubst (fun k : σ =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ y, MvPowerSeries.C (A x y) * MvPowerSeries.X y : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold Formalism.MainNotions.FormalGroupSystem.linSub Formalism.L2.KerInert.Rep.sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul]

variable {p : ℕ} [Fact p.Prime]

theorem subBG_eq {X : Sys p} {D : D7} (E : CEmbC X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) :
    subBG E.toCEmb pos fd j La La' x y = Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La' x y := by
  unfold subBG Formalism.L2.KerInert.RepFrame.subGen
  split_ifs <;> rfl

theorem ltC_eq (g : GL3Theta.G1 p) (hLT : LTIso g) :
    ltC g hLT = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ := by
  unfold ltC Formalism.L2.KerInert.BeCob.eLT
  rw [mul_inv, Units.val_inv_eq_inv_val]

theorem twInt_all (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) : Formalism.L2.KerInert.RepFrame.TwInt X E := by
  intro v s w
  rw [Formalism.L2.KerInert.RepFrob.twE_eq, Formalism.L2.KerInert.RepFrob.twT_alg]
  exact Formalism.L2.G.Pend.norm_wToC_le p _


end Formalism.L2.KerInert.KG
end
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KGLt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert.KG

variable {p : ℕ} [Fact p.Prime]


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_small_of_frame (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by

  let large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) :=
    fun j La _ => fd.kerN j La
  let Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
    fun j _ La' => fd.kerN (j + 1) La'
  let Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')
  let G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')
  let F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => ((p : ℂ_[p]) ^ expG X j La La') •
      TaylorLogMetric.pSer D g.lam (fun z => scalG fd χ muT j La La' * G j La La' z)
  let Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => Formalism.L2.KerInert.Rep.sclY (ltC g hLT) (F j La La')
  let S := fun j (La : X.Lt j) (La' : X.Lt (j + 1)) => Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La'
  have hFam : FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT) =
      fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La') := by
    funext j La La'
    have hS : S j La La' = subBG E.toCEmb pos fd j La La' :=
      funext fun x => funext fun y => (subBG_eq E pos fd j La La' x y).symm
    rw [hS]
    exact linSub_scl _ _ _

  have hB : BeProp p (beLT hLT) := Formalism.L2.KerInert.beProp_ofA Formalism.L2.KerInert.inert_facts_first_hold D cc δ p g hLT hAt h5 hIn hM
  have hComb0 : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg'
      (fun j La La' => TaylorLogMetric.pSer D g.lam (G j La La')) B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_of_dataRec X hfin D B χ SS cl g.lam hcc hδ
      (Formalism.L2.KerInert.AlgTP.algT_of B hcc hδ hχ) large₂ Lg' Ξ
      (Formalism.L2.KerInert.RepRec.dataRec_movD X D cl Ξ₀ (fun j La _ => fd.trG j La) (fun j _ La' => fd.trG (j + 1) La')
        ((Formalism.L2.KerInert.RepRec.dataRec_iff X D cl Ξ₀).2 ⟨hCl, hXi⟩)) hAdm
  have hComb : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_scalar X hfin D large₂ Lg' B.tor (B.eNat χ) g.lam G
      (fun j La La' => scalG fd χ muT j La La') (fun j La La' => expG X j La La') hComb0 hSc
  have hOnb : Formalism.L2.KerInert.RepLt.OnbExLt X hfin D large₂ Lg' :=
    Formalism.L2.KerInert.RepLt.onbExLt_of X hfin D large₂ Lg'
      (Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four Formalism.L2.KerInert.weakApprox_of_approx_and_separation) h5 hIn hAdm
  have hTr : Formalism.L2.KerInert.RepLt.LamTraceLt X hfin D large₂ Lg' g.lam :=
    Formalism.L2.KerInert.RepLt.lamTraceLt_of X hfin D large₂ Lg' g.lam
      (Formalism.L2.KerInert.RepLt.rankTieLt_of X hfin D large₂ Lg' hAdm)
      (Formalism.L2.KerInert.RepFrame.colTie_of X hfin D large₂ Lg' (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) g.lam)
  have hFH : Formalism.L2.KerInert.RepLt.FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1 :=
    Formalism.L2.KerInert.RepLt.frameHypLt_of_lat X E hfin D pos large₂ Lg' fd.frM g.lam ρ hOnb hTr hρ
      (Formalism.L2.KerInert.RepFrob.frobTw_of X E h5) hMI (twInt_all X E) hL Fr
  rw [hFam]
  exact Formalism.L2.KerInert.RepLt.K1_representatives_LT_of_dictionary Formalism.L2.KerInert.Rep.curve_dictionary Formalism.L2.KerInert.kernels_integral_inert D h5 X E
    hfin hLT cc δ hAt hIn hM B hcc hδ χ hχ hIn hLam pos large₂ Lg' F Fr
    (fun j La La' => by simp only [Fr]; rw [ltC_eq]) S hB hComb hFH


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_small_of_frame_twist (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : XiAwayLt X hfin D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by
  classical
  let Ξ₁ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => if j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2 then Ξ₀ j La La' else fun _ => 0
  have hXi1 : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₁ := by
    obtain ⟨S₀, hp, hS⟩ := hXi
    refine ⟨S₀, hp, fun j La La' y => ?_⟩
    by_cases h : j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [Ξ₁, if_pos h]
      exact hS j h.1 La h.2.1 La' h.2.2 y
    · simp only [Ξ₁, if_neg h]
      exact IntOff.zero
  have hK := first_kernel_small_of_frame D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₁ muT ρ hAt hIn hM hcc hδ hχ hLam
    hAdm hCl hXi1 hSc hρ hMI hL
  intro j hj L0 h0 La' hLa' φ
  have hEq : thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₁ muT (ltC g hLT)) j L0 La' =
      thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) j L0 La' := by
    simp only [thFOf, FrecG, Ξ₁, if_pos (And.intro hj (And.intro h0 hLa'))]
  have := hK j hj L0 h0 La' hLa' φ
  rwa [hEq] at this


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_law_global_small : TranslatesOfInertKernelAtPlace := by
  intro D p _ h5 X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hlam hLam hAdm hCl hXi hSc
    hρ hMI hL
  subst hlam
  have hK := first_kernel_small_of_frame_twist D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hLam hAdm hCl hXi hSc
    hρ hMI hL
  have h2b := (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos _).2 hK
  exact ⟨Formalism.L2.KerInert.admissible_second_of_variant D X E hfin hst hLT pos _ h2b, h2b,
    Formalism.L2.KerInert.admissible_third_of_second_eleventh D X E hfin hst hLT pos _ h2b
      (Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hIn hM X _ rfl)⟩

end Formalism.L2.KerInert.KGLt
end
end
end
