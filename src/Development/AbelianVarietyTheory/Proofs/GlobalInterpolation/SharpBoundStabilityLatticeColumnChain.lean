module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernelStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModelsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernelStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  first | exact @GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | exact GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | (intros; apply GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.exists_levelPrimePointModel_realisation : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T), ∃ M : PtModel B.ch i, Nonempty (B.Real i sp M) := by
  first | exact @GlobalTheory.LvT.Built.RealM.exists_real | exact GlobalTheory.LvT.Built.RealM.exists_real | (intros; apply GlobalTheory.LvT.Built.RealM.exists_real <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntPOfKerP

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdCardStabilizerForm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

end Record

end GlobalTheory.LvT.StabOrder
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg

section

@[expose] public section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dite_eq_right hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dite_eq_left hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SharpBoundStabilityLatticeColumnChain

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.LvT.Built.Assemble

theorem sharpBound_stability_latticeColumnChain : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u),
    (∀ i, i ≤ D.R.m → Nonempty (Split (B.J.A i) B.J.T)) → B.Sees →
    (∀ i, i < D.R.m → ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧ Built.Dat.KerBar k ∧
      Built.Dat.KerP k) →
    Module.finrank ℚ B.E * D.R.N D.R.m + 1 < B.J.T → TwColumn.WtSigns B.ch → Conclusion5Sharp B.ch ∧ FormsStable B.ch := by
  intro D u B hsp hsee hker hT hW

  have hM : ∀ i (h : i ≤ D.R.m), ∃ M : PtModel B.ch i, Nonempty (B.Real i (hsp i h).some M) :=
    fun i h => GlobalTheory.T.exists_levelPrimePointModel_realisation D u B i (hsp i h).some
  let Lv : LevTie B.ch := fun i h => (hM i h).choose
  have hR : ∀ i (h : i ≤ D.R.m), B.Real i (hsp i h).some (Lv i h) := fun i h => (hM i h).choose_spec.some

  have hC : ∀ i (h : i ≤ D.R.m), ∃ Co : (Lv i h).Coord, Co.Ok ∧ (hR i h).ValIs Co :=
    fun i h => GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices D u B i (hsp i h).some (Lv i h) (hR i h) h hsee
  let Vt : ValTie Lv := fun i h => ⟨(hC i h).choose, (hC i h).choose_spec.1⟩

  have hk : ∀ i (h : i < D.R.m), ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧
      Built.Dat.KerBar k ∧ Built.Dat.KerP k := hker

  have hK : ∀ i (h : i < D.R.m), ∃ K : KerPt (Lv i h.le) (Lv (i + 1) h),
      K.TgtEq ∧ Built.Dat.KerIs (hR i h.le) (hR (i + 1) h) K (hk i h).choose :=
    fun i h => GlobalTheory.T.exists_pointKernel_realised_models D u B i (hsp i h.le).some (hsp (i + 1) h).some (Lv i h.le) (Lv (i + 1) h)
      (hR i h.le) (hR (i + 1) h) _ (hk i h).choose_spec.1
  let Kt : KerTie Lv := fun i h => (hK i h).choose
  have laws : KerLaws Vt Kt :=
    { tgt := fun i h => (hK i h).choose_spec.1
      dil := fun i h => GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.1
      uk := fun i h => GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.2.1
      bar := fun i h => GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.1
      intP := fun i h => IntPPass.intP_of_kerP D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.2 }
  have hF : FormsStable B.ch := formsStable_of_tgtEq D u B.ch Lv Kt laws.tgt
  have h4 : LevelChainUOperatorCommutation B.ch := levelChainUOperatorCommutation_of_pointPairLaw D u B.ch Lv Kt laws.tgt laws.uk
  have hst : StabUnit B.ch := StabOrder.stabUnit_of_chainIn B.ch B.I B.emb D.what₂.embLL B.hI rfl hT
  have hWb : WtBounds B.ch := wtBounds_of_nonneg D u B.ch hW.1 hW.2
  exact ⟨levelChainSharpColumnValuation_of_stability D u B.ch hF h4 (UKS.ukSharp D u B.ch Lv Vt Kt laws hst hWb) hWb, hF⟩

end GlobalTheory.LvT.Built.Assemble
end
end
