module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
public import Development.AutomorphicArithmetic.DivisorFrames.ArithmeticFunctionInducedBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.CovCmp
open scoped Classical

theorem UpperTheory.norms_give_rational_sections :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (V : Mean4O.Cover Y) (L : HermLB V.p) (m : ℕ) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), Norms V L (fun x => genAt A.D x ^ m) a (fun v e y => (m : ℝ) * A.lg v e y) → ∃ s : L.B.ι → V.X.functionFieldˣ, ∀ v, CRead V v L.B s fun e y => (m : ℝ) * VertCmp.lam A v e y := by
  intro F _ _ Y C A V L m a h
  have hLift : ∃ (s : L.B.ι → V.X.functionFieldˣ) (_ : IsRatSec L.B s),
      ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y)
        (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (i : L.B.ι),
        z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U i →
        let g := V.φ (genAt A.D (below y.1) ^ m) *
          SmallSec.fnMap V.j (Isom.j_gen_specializes V) (s i)
        UnitAt (below z) g ∧ (m : ℝ) * A.lg v e y = Real.log (e.w (TrueGeo.valAt z g)) := by
    obtain ⟨r, hr, hu, -, hf⟩ := h
    have := CoverHt.isPreimmersion_j V
    have hη := Isom.j_gen_specializes V
    let ρ : V.X.functionField ≃+* V.G.functionField :=
      RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
        ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
    have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U)
        (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (t : Γ(V.X, U)),
        ρ (fnOf U hU t) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U t) :=
      fun U hU hU' t => SmallSec.fnMap_fnOf V.j hη hU hU' t
    have hj : V.j (genericPoint V.G) = genericPoint V.X :=
      (hη.antisymm (genericPoint_specializes _)).eq
    refine ⟨_, InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr, fun v e y z yt i e₁ e₂ hU => ?_⟩
    have eρ : SmallSec.fnMap V.j hη
        ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField) =
        (r fun _ => i : V.G.functionField) := ρ.apply_symm_apply _
    dsimp only
    rw [eρ]
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have hmem : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt
    have hw := hu _ _ hmem
    have hb : V.π (below z) = below y.1 := by rw [← e₁]; rfl
    rw [hb] at hw
    exact ⟨hw, hf v e y z yt (fun _ => i) e₁ e₂ hU⟩
  obtain ⟨s, hs, hR⟩ := hLift
  obtain ⟨W, hW, hE⟩ := (A.D.isEqn_genericPoint 1).exists_nhds
  have hu (x : Y.X) (hx : x ∈ W) : UnitAt x (eqn A.D x : Y.Fn) := by
    simpa using (hE x hx).iff_unitAt.1 (Base.isEqn_eqn A.D x)
  have hf (x : Y.X) (hx : x ∈ W) : UnitAt x (genAt A.D x ^ m) := by
    rw [genAt, Units.val_inv_eq_inv_val]
    clear hR h
    induction m with
    | zero => simpa using unitAt_one x
    | succ n ih => rw [pow_succ]; exact ih.mul (hu x hx).inv
  refine ⟨s, fun v => ⟨hs, W, hW, fun e y z yt i hy e₁ e₂ hU _ => ?_⟩⟩
  have := CoverHt.isPreimmersion_j V
  obtain ⟨hw, H⟩ := hR v e y z yt i e₁ e₂ hU
  obtain ⟨hπ, eφ⟩ := V.φ_eq_fnMap
  have hb : V.π (below z) = below y.1 := by rw [← e₁]; rfl
  have hfy := hf _ hy
  have hfz : UnitAt (below z) (V.φ (genAt A.D (below y.1) ^ m)) := by
    rw [eφ]
    exact unitAt_fnMap_of V.π hπ (by rw [hb]; exact hfy)
  have hs' := hfz.inv.mul hw
  rw [inv_mul_cancel_left₀ hfz.ne_zero] at hs'
  have hval : TrueGeo.valAt z (V.φ (genAt A.D (below y.1) ^ m)) =
      TrueGeo.valAt y.1 (genAt A.D (below y.1) ^ m) := by
    rw [eφ, SmallSec.valAt_fnMap V.π hπ z (by rw [hb]; exact hfy.regAt), e₁]
  rw [SmallSec.valAt_mul hfz.regAt hs'.regAt, map_mul,
    Real.log_mul (e.w.pos (Res.valAt_ne_zero hfz)).ne' (e.w.pos (Res.valAt_ne_zero hs')).ne', hval,
    genAt, Units.val_inv_eq_inv_val, Res.valAt_pow (hu _ hy).inv.regAt, LineNorm.Neg.valAt_inv (hu _ hy),
    AbsoluteValue.map_pow, map_inv₀, Real.log_pow, Real.log_inv] at H
  beta_reduce at H ⊢
  rw [VertCmp.lam, ModelFn.valAt_comp V.j (Isom.j_gen_specializes V) z, mul_add, H]
  ring
