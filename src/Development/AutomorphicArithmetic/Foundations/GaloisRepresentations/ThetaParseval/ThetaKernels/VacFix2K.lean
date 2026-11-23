module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadStmt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.WeilBound.ThetaLifts.LatticeBasics.CompCA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIntAddConjEqOneOfBaseGoodK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertK
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocConeVfEig
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsBetaK

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}
theorem exists_res_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases _root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_, splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp]; exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
theorem exists_beta_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 := by
  have hσ := cm_conj_conj hB.cm
  have cc := cA_cA (F := F) hσ
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_res_k hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX).ne_zero hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ, map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k

      simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add (f := _), jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, map_zero]))
    (inj (by
      rw [map_add (f := _), map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add (f := _), map_one, ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)] at k1 k2 k4 k5
    rw [map_add (f := _), k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _), map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu => Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add (f := _), map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add (f := _), add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩
end GlobalTheory.ThK.Dbl.Vf2
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.VacFix2K

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone.Vf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
theorem _root_.GlobalTheory.ThK.Dbl.vacFix2_k : _root_.GlobalTheory.ThK.Dbl.VacFix2_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1 := by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this,
        zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg']; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]
end GlobalTheory.ThK.Dbl.Vf2
end
end
end
end
