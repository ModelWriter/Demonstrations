/**
 * Copyright (c) 2013 itemis AG and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     Mark Broerkens - initial API and implementation
 * 
 */
package org.eclipse.rmf.reqif10.impl;

import java.math.BigInteger;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.rmf.reqif10.DatatypeDefinitionReal;
import org.eclipse.rmf.reqif10.ReqIF10Package;

/**
 * <!-- begin-user-doc --> An implementation of the model object '<em><b>Datatype Definition Real</b></em>'. <!--
 * end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 * <li>{@link org.eclipse.rmf.reqif10.impl.DatatypeDefinitionRealImpl#getAccuracy <em>Accuracy</em>}</li>
 * <li>{@link org.eclipse.rmf.reqif10.impl.DatatypeDefinitionRealImpl#getMax <em>Max</em>}</li>
 * <li>{@link org.eclipse.rmf.reqif10.impl.DatatypeDefinitionRealImpl#getMin <em>Min</em>}</li>
 * </ul>
 * </p>
 * 
 * @generated
 */
public class DatatypeDefinitionRealImpl extends DatatypeDefinitionSimpleImpl implements DatatypeDefinitionReal {
	/**
	 * The default value of the '{@link #getAccuracy() <em>Accuracy</em>}' attribute. <!-- begin-user-doc --> <!--
	 * end-user-doc -->
	 * 
	 * @see #getAccuracy()
	 * @generated
	 * @ordered
	 */
	protected static final BigInteger ACCURACY_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getAccuracy() <em>Accuracy</em>}' attribute. <!-- begin-user-doc --> <!--
	 * end-user-doc -->
	 * 
	 * @see #getAccuracy()
	 * @generated
	 * @ordered
	 */
	protected BigInteger accuracy = ACCURACY_EDEFAULT;

	/**
	 * This is true if the Accuracy attribute has been set. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 * @ordered
	 */
	protected boolean accuracyESet;

	/**
	 * The default value of the '{@link #getMax() <em>Max</em>}' attribute. <!-- begin-user-doc --> <!-- end-user-doc
	 * -->
	 * 
	 * @see #getMax()
	 * @generated
	 * @ordered
	 */
	protected static final double MAX_EDEFAULT = 0.0;

	/**
	 * The cached value of the '{@link #getMax() <em>Max</em>}' attribute. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @see #getMax()
	 * @generated
	 * @ordered
	 */
	protected double max = MAX_EDEFAULT;

	/**
	 * This is true if the Max attribute has been set. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 * @ordered
	 */
	protected boolean maxESet;

	/**
	 * The default value of the '{@link #getMin() <em>Min</em>}' attribute. <!-- begin-user-doc --> <!-- end-user-doc
	 * -->
	 * 
	 * @see #getMin()
	 * @generated
	 * @ordered
	 */
	protected static final double MIN_EDEFAULT = 0.0;

	/**
	 * The cached value of the '{@link #getMin() <em>Min</em>}' attribute. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @see #getMin()
	 * @generated
	 * @ordered
	 */
	protected double min = MIN_EDEFAULT;

	/**
	 * This is true if the Min attribute has been set. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 * @ordered
	 */
	protected boolean minESet;

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	protected DatatypeDefinitionRealImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return ReqIF10Package.Literals.DATATYPE_DEFINITION_REAL;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public BigInteger getAccuracy() {
		return accuracy;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void setAccuracy(BigInteger newAccuracy) {
		BigInteger oldAccuracy = accuracy;
		accuracy = newAccuracy;
		boolean oldAccuracyESet = accuracyESet;
		accuracyESet = true;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY, oldAccuracy, accuracy,
					!oldAccuracyESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void unsetAccuracy() {
		BigInteger oldAccuracy = accuracy;
		boolean oldAccuracyESet = accuracyESet;
		accuracy = ACCURACY_EDEFAULT;
		accuracyESet = false;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.UNSET, ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY, oldAccuracy,
					ACCURACY_EDEFAULT, oldAccuracyESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public boolean isSetAccuracy() {
		return accuracyESet;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public double getMax() {
		return max;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void setMax(double newMax) {
		double oldMax = max;
		max = newMax;
		boolean oldMaxESet = maxESet;
		maxESet = true;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX, oldMax, max, !oldMaxESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void unsetMax() {
		double oldMax = max;
		boolean oldMaxESet = maxESet;
		max = MAX_EDEFAULT;
		maxESet = false;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.UNSET, ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX, oldMax, MAX_EDEFAULT, oldMaxESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public boolean isSetMax() {
		return maxESet;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public double getMin() {
		return min;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void setMin(double newMin) {
		double oldMin = min;
		min = newMin;
		boolean oldMinESet = minESet;
		minESet = true;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN, oldMin, min, !oldMinESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void unsetMin() {
		double oldMin = min;
		boolean oldMinESet = minESet;
		min = MIN_EDEFAULT;
		minESet = false;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.UNSET, ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN, oldMin, MIN_EDEFAULT, oldMinESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public boolean isSetMin() {
		return minESet;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY:
			return getAccuracy();
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX:
			return getMax();
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN:
			return getMin();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY:
			setAccuracy((BigInteger) newValue);
			return;
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX:
			setMax((Double) newValue);
			return;
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN:
			setMin((Double) newValue);
			return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public void eUnset(int featureID) {
		switch (featureID) {
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY:
			unsetAccuracy();
			return;
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX:
			unsetMax();
			return;
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN:
			unsetMin();
			return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID) {
		switch (featureID) {
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__ACCURACY:
			return isSetAccuracy();
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MAX:
			return isSetMax();
		case ReqIF10Package.DATATYPE_DEFINITION_REAL__MIN:
			return isSetMin();
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public String toString() {
		if (eIsProxy())
			return super.toString();

		StringBuffer result = new StringBuffer(super.toString());
		result.append(" (accuracy: "); //$NON-NLS-1$
		if (accuracyESet)
			result.append(accuracy);
		else
			result.append("<unset>"); //$NON-NLS-1$
		result.append(", max: "); //$NON-NLS-1$
		if (maxESet)
			result.append(max);
		else
			result.append("<unset>"); //$NON-NLS-1$
		result.append(", min: "); //$NON-NLS-1$
		if (minESet)
			result.append(min);
		else
			result.append("<unset>"); //$NON-NLS-1$
		result.append(')');
		return result.toString();
	}

} // DatatypeDefinitionRealImpl
