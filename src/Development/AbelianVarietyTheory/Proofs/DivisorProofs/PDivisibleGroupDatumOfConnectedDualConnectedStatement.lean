module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfSubsingletonPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransport

section

@[expose] public section

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def omegaDualCongr {G H : PDivGroup p O} (f : G ≅ H) : G.dual.omega ≃ₗ[O] H.dual.omega :=
  LinearEquiv.ofLinearMap (omegaDualMap G H f.hom) (omegaDualMap H G f.inv)
    (by rw [← omegaDualMap_comp, f.inv_hom_id, omegaDualMap_id])
    (by rw [← omegaDualMap_comp, f.hom_inv_id, omegaDualMap_id])

def lieCongr {G H : PDivGroup p O} (f : G ≅ H) : G.Lie ≃ₗ[O] H.Lie :=
  LinearEquiv.ofLinearMap (lieMap G H f.hom) (lieMap H G f.inv)
    (by rw [← lieMap_comp, f.inv_hom_id, lieMap_id])
    (by rw [← lieMap_comp, f.hom_inv_id, lieMap_id])

theorem datum_transport [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {h : ℕ}
    {G H : PDivGroup p O} (f : G ≅ H) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie)
    (h1 : ∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O))
    (h2 : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)) :
    ∃ (e' : H.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
      (fil' : H.dual.omega ≃ₗ[O] D.Fil) (lie' : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] H.Lie),
      (∀ t, D.al (toO e' t) = (fil' (hodgeTate H t) : Fin h → O)) ∧
        ∀ (x : H.Lie) (χ : H.dual.Tate), pairingO hε e' (bQuot D (lie'.symm x)) χ = x (dlog H χ) := by
  refine ⟨(tateCongr O f).symm ≪≫ₗ e, (omegaDualCongr f).symm ≪≫ₗ fil, lie ≪≫ₗ lieCongr f,
    fun s => ?_, fun x χ => ?_⟩
  · have := h1 (tateMap H G O f.inv s)
    change D.al (toO e (tateMap H G O f.inv s)) =
      (fil (omegaDualMap H G f.inv (hodgeTate H s)) : Fin h → O)
    rw [this, ← hodgeTate_tateMap]
  · set χ' := tateMap _ _ O (dualHom G H f.hom) χ
    have hp : ∀ y, pairingO hε ((tateCongr O f).symm ≪≫ₗ e) y χ = pairingO hε e y χ' := by
      intro y
      simp only [pairingO, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      simp only [epsPairing, tateCongr_apply, pairing_tateMap, χ']
    have hl : (lie ≪≫ₗ lieCongr f).symm x = lie.symm (lieMap H G f.inv x) := rfl
    rw [hp, hl, h2, lieMap_apply, dlog_tateMap, ← LinearMap.comp_apply (omegaMap H G f.inv),
      ← omegaMap_comp, f.inv_hom_id, omegaMap_id, LinearMap.id_apply]

theorem hasDatum_of_iso : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G H : PDivGroup p O,
      Nonempty (G ≅ H) → HasDatum hε G → HasDatum hε H := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H ⟨f⟩ hG
  haveI : IsIntegrallyClosedIn O C :=
    isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun hx => hv.exists_of_le_one
      (hv.isIntegral_iff_v_le_one.1 hx)⟩
  have hh : G.height = H.height := by
    rw [← PDivGroup.finrank_tate G C, ← PDivGroup.finrank_tate H C]
    exact (tateCongr O f).finrank_eq
  obtain ⟨D, e, fil, lie, h1, h2⟩ := hG
  unfold HasDatum
  rw [← hh]
  obtain ⟨e', fil', lie', h1', h2'⟩ := datum_transport hε f D e fil lie h1 h2
  exact ⟨D, e', fil', lie', h1', h2'⟩

end GlobalTheory.PDivLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRep

section

@[expose] public section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

end Group

end GlobalTheory.DetInv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToLinTransposeDot

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualDatumDot

def dotL {O : Type} [CommRing O] {h : ℕ} (u : Fin h → O) : (Fin h → O) →ₗ[O] O where
  toFun m := u ⬝ᵥ m
  map_add' a b := dotProduct_add u a b
  map_smul' c m := by simp

theorem dot_single {O : Type} [CommRing O] {h : ℕ} (g : (Fin h → O) →ₗ[O] O) (x : Fin h → O) :
    (fun i => g (Pi.single i 1)) ⬝ᵥ x = g x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp [map_sum, dotProduct, mul_comm]

theorem toLin'_transpose_dot {A O : Type} [CommRing A] [CommRing O] (θ : A →+* O) {h : ℕ}
    (X : Matrix (Fin h) (Fin h) A) (a b : Fin h → O) :
    Matrix.toLin' (Xᵀ.map θ) a ⬝ᵥ b = a ⬝ᵥ Matrix.toLin' (X.map θ) b := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.transpose_map, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

end GlobalTheory.DualDatumDot

open GlobalTheory.DualDatumDot

namespace GlobalTheory.DualDatum

theorem hasDatum_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → HasDatum hε G.dual := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G ⟨D, e, fil, lie, hA, hB⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hζ
  have hν' : nu ε ≠ 0 := fun h0 => hν (by rw [h0, map_zero])
  have hμ : Sandwich.mu ε ≠ 0 := by rw [← xi_mul_nu]; exact mul_ne_zero hξ hν'
  obtain ⟨-, h1, -, h3, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  haveI := hfin
  haveI := hproj
  let θ := WittVector.fontaineTheta O p
  let D' := SelfDualFil.dualDatum hμ hξ D

  have perp : ∀ a, a ∈ D'.Fil ↔ ∀ f ∈ D.Fil, a ⬝ᵥ f = 0 := by
    intro a
    change Matrix.toLin' ((D.F)ᵀ.map θ) a = 0 ↔ _
    constructor
    · intro ha f hf
      obtain ⟨w, hw⟩ := h3 f hf
      have e1 : a ⬝ᵥ D.al w = 0 := by
        rw [show D.al w = Matrix.toLin' (D.F.map θ) w from rfl, ← toLin'_transpose_dot, ha,
          zero_dotProduct]
      rw [hw, dotProduct_smul, smul_eq_mul] at e1
      exact (mul_eq_zero.1 e1).resolve_left hν
    · intro ha
      funext i
      have h2 := ha _ (h1 ⟨Pi.single i 1, rfl⟩)
      rw [show D.al (Pi.single i 1) = Matrix.toLin' (D.F.map θ) (Pi.single i 1) from rfl,
        ← toLin'_transpose_dot] at h2
      simpa using h2

  let E : Fin G.height → G.Tate := fun i => e.symm (Pi.single i 1)
  have hexp : ∀ t, t = ∑ i, e t i • E i := by
    intro t
    apply e.injective

    rw [map_sum]
    ext j
    simp [E, Finset.sum_apply, Pi.single_apply]
  let L : G.dual.Tate →ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearMap.pi fun i => (epsEquiv hε).symm.toLinearMap ∘ₗ pairing G O (E i)
  have hL : ∀ χ i, L χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hflip := G.pairing_flip_bijective C
  have hLb : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun χ hχ => hflip.1 ?_
      rw [map_zero]
      refine LinearMap.ext fun t => ?_

      rw [LinearMap.flip_apply, LinearMap.zero_apply, hexp t, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← epsPairing_smul hε, ← hL, hχ]
      simp
    · intro c
      let φ : G.Tate →ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
        (epsEquiv hε).toLinearMap ∘ₗ (∑ i, c i • LinearMap.proj i) ∘ₗ e.toLinearMap
      obtain ⟨χ, hχ⟩ := hflip.2 φ
      refine ⟨χ, funext fun j => ?_⟩
      have hj : pairing G O (E j) χ = φ (E j) := LinearMap.congr_fun hχ (E j)
      rw [hL, epsPairing, hj]
      simp [φ, E, Pi.single_apply]
  let e' : G.dual.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) := LinearEquiv.ofBijective L hLb
  have he' : ∀ χ i, e' χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hdualb : ∀ t i, epsPairing hε G t (e'.symm (Pi.single i 1)) = e t i := by
    intro t i
    have hj : ∀ j, epsPairing hε G (E j) (e'.symm (Pi.single i 1)) = (Pi.single i (1 : ℤ_[p]) : Fin G.height → ℤ_[p]) j := by
      intro j
      rw [← he', LinearEquiv.apply_symm_apply]
    have hs : ∀ s, epsPairing hε G s (e'.symm (Pi.single i 1)) =
        (epsEquiv hε).symm.toLinearMap ((pairing G O).flip (e'.symm (Pi.single i 1)) s) :=
      fun _ => rfl
    rw [hs]
    conv_lhs => rw [hexp t]

    rw [map_sum, map_sum]
    simp only [map_smul, ← hs, hj, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let Φ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  let g : G.omega → (Fin G.height → O) →ₗ[O] O := fun w =>
    Module.Dual.eval O G.omega w ∘ₗ lie.toLinearMap ∘ₗ D.Fil.mkQ
  have hΦdot : ∀ w m, Φ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := fun w m => dot_single (g w) m
  have hΦmem : ∀ w, Φ w ∈ D'.Fil := fun w => (perp _).2 fun f hf => by
    rw [hΦdot, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hf, map_zero,
      LinearMap.zero_apply]
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun w hw => ?_
    apply (Module.evalEquiv O G.omega).injective
    rw [map_zero]
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ := lie.surjective x
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.zero_apply, ← hΦdot, hw,
      zero_dotProduct]
  have hΦsurj : ∀ u ∈ D'.Fil, ∃ w, Φ w = u := by
    intro u hu
    have hle : D.Fil ≤ LinearMap.ker (dotL u) := fun f hf => (perp u).1 hu f hf
    let ℓ : G.Lie →ₗ[O] O := D.Fil.liftQ (dotL u) hle ∘ₗ lie.symm.toLinearMap
    refine ⟨(Module.evalEquiv O G.omega).symm ℓ, funext fun i => ?_⟩
    have hw : ∀ x : G.Lie, x ((Module.evalEquiv O G.omega).symm ℓ) = ℓ x := fun x => by
      have h5 := LinearMap.congr_fun ((Module.evalEquiv O G.omega).apply_symm_apply ℓ) x
      rwa [Module.evalEquiv_apply, Module.Dual.eval_apply] at h5
    change lie (D.Fil.mkQ (Pi.single i 1)) _ = u i
    rw [hw]
    change D.Fil.liftQ (dotL u) hle (lie.symm (lie (D.Fil.mkQ (Pi.single i 1)))) = u i
    rw [LinearEquiv.symm_apply_apply]
    change u ⬝ᵥ Pi.single i 1 = u i
    simp
  let filE : G.omega ≃ₗ[O] D'.Fil := LinearEquiv.ofBijective (Φ.codRestrict D'.Fil hΦmem)
    ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), fun u => by
      obtain ⟨w, hw⟩ := hΦsurj u.1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩
  let fil' : G.dual.dual.omega ≃ₗ[O] D'.Fil := (DlogSpan.pDivGroupOmegaBidualEquiv G).symm ≪≫ₗ filE

  let Ψ : (Fin G.height → O) →ₗ[O] G.dual.Lie :=
    LinearMap.mk₂ O (fun m w => m ⬝ᵥ (fil w : Fin G.height → O))
      (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [dotProduct_add]) (fun _ _ _ => by simp)
  have hΨ : ∀ m w, Ψ m w = m ⬝ᵥ (fil w : Fin G.height → O) := fun _ _ => rfl
  have hΨker : LinearMap.ker Ψ = D'.Fil := by
    ext m
    rw [LinearMap.mem_ker, perp]
    constructor
    · intro hm f hf
      obtain ⟨w, hw⟩ := fil.surjective ⟨f, hf⟩
      have h5 := LinearMap.congr_fun hm w
      rwa [hΨ, hw] at h5
    · intro hm
      exact LinearMap.ext fun w => hm _ (fil w).2
  haveI : Module.Projective O ((Fin G.height → O) ⧸ D.Fil) := Module.Projective.of_equiv lie.symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property D.Fil.mkQ LinearMap.id D.Fil.mkQ_surjective
  let r : (Fin G.height → O) →ₗ[O] D.Fil :=
    (LinearMap.id - s ∘ₗ D.Fil.mkQ).codRestrict D.Fil fun x => by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
      have h5 := LinearMap.congr_fun hs (D.Fil.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h5 ⊢
      rw [h5, sub_self]
  have hr : ∀ f : D.Fil, r f = f := fun f => by
    apply Subtype.ext
    have h0 : D.Fil.mkQ (f : Fin G.height → O) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 f.2
    simp [r, h0]
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    let φ : (Fin G.height → O) →ₗ[O] O := y ∘ₗ fil.symm.toLinearMap ∘ₗ r
    refine ⟨fun i => φ (Pi.single i 1), LinearMap.ext fun w => ?_⟩
    rw [hΨ, dot_single]
    simp [φ, hr]
  let lie' : ((Fin G.height → O) ⧸ D'.Fil) ≃ₗ[O] G.dual.Lie :=
    Submodule.quotEquivOfEq _ _ hΨker.symm ≪≫ₗ Ψ.quotKerEquivOfSurjective hΨsurj
  have hlie' : ∀ m, lie' (D'.Fil.mkQ m) = Ψ m := fun _ => rfl
  refine ⟨D', e', fil', lie', fun χ => ?_, fun y ψ => ?_⟩
  · have hf : fil' (hodgeTate G.dual χ) = filE (dlog G χ) := by
      simp only [fil', LinearEquiv.trans_apply]
      congr 1
      rw [LinearEquiv.symm_apply_eq, DlogSpan.pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate]
    rw [hf]
    change _ = Φ (dlog G χ)
    funext i
    change _ = lie (D.Fil.mkQ (Pi.single i 1)) (dlog G χ)
    rw [← hB, LinearEquiv.symm_apply_apply]
    change Matrix.toLin' ((D.G)ᵀ.map θ) (toO e' χ) i =
      pairingO hε e (Matrix.toLin' (D.G.map θ) (Pi.single i 1)) χ
    simp [pairingO, toO, he', E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, θ,
      Pi.single_apply, mul_comm]
  · obtain ⟨m, rfl⟩ := hΨsurj y
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective ψ
    have hl : lie'.symm (Ψ m) = D'.Fil.mkQ m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hlie' m).symm
    rw [hl]
    change pairingO hε e' (D'.bb m) (tateMap G G.dual.dual O G.bidual.hom t) =
      Ψ m (dlog G.dual (tateMap G G.dual.dual O G.bidual.hom t))
    rw [← hodgeTate_apply, hΨ, ← hA]
    have hp : ∀ i, epsPairing hε G.dual (e'.symm (Pi.single i 1))
        (tateMap G G.dual.dual O G.bidual.hom t) = e t i := fun i => by
      rw [epsPairing, DetInv.pairing_dual_bidual]
      exact hdualb t i
    simp only [pairingO, hp]
    change Matrix.toLin' ((D.F)ᵀ.map θ) m ⬝ᵥ toO e t = m ⬝ᵥ Matrix.toLin' (D.F.map θ) (toO e t)
    rw [toLin'_transpose_dot]

end GlobalTheory.DualDatum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem isConn_of_retract {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Nontrivial O] {G H : PDivGroup p O}
    (f : H ⟶ G) (r : G ⟶ H) (h : f ≫ r = 𝟙 H) (hG : GlobalTheory.PDivLat.IsConn G) : GlobalTheory.PDivLat.IsConn H := by
  intro n
  have hs : Function.Surjective (f.app n) := fun a => ⟨r.app n a, by
    have := congrArg (fun g => Hom.app g n) h
    exact DFunLike.congr_fun this a⟩
  haveI : Nontrivial (H.A n) :=
    (Bialgebra.counitAlgHom O (H.A n) : H.A n →+* O).domain_nontrivial
  haveI := hG n
  exact IsLocalRing.of_surjective' (f.app n : G.A n →+* H.A n) hs

theorem hasDatum_of_conn_dual_conn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hyp G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨G₁, G₂, hs, hc₁, hk₂⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G
  obtain ⟨H₁, H₂, hs', hcH, hkH⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G₁.dual
  obtain ⟨i₁, -, q₁, -, e₁, -⟩ := id hs'
  have hD : GlobalTheory.PDivLat.IsConn H₁.dual :=
    isConn_of_retract (dualHom _ _ q₁ ≫ G₁.bidual.inv) (G₁.bidual.hom ≫ dualHom _ _ i₁)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, ← dualHom_comp, e₁, dualHom_id]) hc₁
  have dD := GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε _ _ _ hs' (hyp H₁ hcH hD)
    (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε H₂ hkH)
  have d₁ := GlobalTheory.PDivLat.hasDatum_of_iso p C v O hv ε hε _ _ ⟨G₁.bidual.symm⟩
    (GlobalTheory.DualDatum.hasDatum_dual p C v O hv ε hε _ dD)
  exact GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε G G₁ G₂ hs d₁ (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε G₂ hk₂)

end GlobalTheory.PDivLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnectedStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivisibleGroup_datum_of_connected_dual_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  first | exact @GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | exact GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | (intros; apply GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn <;> assumption)
end
end
