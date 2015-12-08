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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.rmf.reqif10.AttributeDefinitionReal;
import org.eclipse.rmf.reqif10.AttributeValueReal;
import org.eclipse.rmf.reqif10.ReqIF10Package;

/**
 * <!-- begin-user-doc --> An implementation of the model object '<em><b>Attribute Value Real</b></em>'. <!--
 * end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 * <li>{@link org.eclipse.rmf.reqif10.impl.AttributeValueRealImpl#getTheValue <em>The Value</em>}</li>
 * <li>{@link org.eclipse.rmf.reqif10.impl.AttributeValueRealImpl#getDefinition <em>Definition</em>}</li>
 * </ul>
 * </p>
 * 
 * @generated
 */
public class AttributeValueRealImpl extends AttributeValueSimpleImpl implements AttributeValueReal {
	/**
	 * The default value of the '{@link #getTheValue() <em>The Value</em>}' attribute. <!-- begin-user-doc --> <!--
	 * end-user-doc -->
	 * 
	 * @see #getTheValue()
	 * @generated
	 * @ordered
	 */
	protected static final double THE_VALUE_EDEFAULT = 0.0;

	/**
	 * The cached value of the '{@link #getTheValue() <em>The Value</em>}' attribute. <!-- begin-user-doc --> <!--
	 * end-user-doc -->
	 * 
	 * @see #getTheValue()
	 * @generated
	 * @ordered
	 */
	protected double theValue = THE_VALUE_EDEFAULT;

	/**
	 * This is true if the The Value attribute has been set. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 * @ordered
	 */
	protected boolean theValueESet;

	/**
	 * The cached value of the '{@link #getDefinition() <em>Definition</em>}' reference. <!-- begin-user-doc --> <!--
	 * end-user-doc -->
	 * 
	 * @see #getDefinition()
	 * @generated
	 * @ordered
	 */
	protected AttributeDefinitionReal definition;

	/**
	 * This is true if the Definition reference has been set. <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 * @ordered
	 */
	protected boolean definitionESet;

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	protected AttributeValueRealImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return ReqIF10Package.Literals.ATTRIBUTE_VALUE_REAL;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public double getTheValue() {
		return theValue;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void setTheValue(double newTheValue) {
		double oldTheValue = theValue;
		theValue = newTheValue;
		boolean oldTheValueESet = theValueESet;
		theValueESet = true;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE, oldTheValue, theValue,
					!oldTheValueESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void unsetTheValue() {
		double oldTheValue = theValue;
		boolean oldTheValueESet = theValueESet;
		theValue = THE_VALUE_EDEFAULT;
		theValueESet = false;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.UNSET, ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE, oldTheValue, THE_VALUE_EDEFAULT,
					oldTheValueESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public boolean isSetTheValue() {
		return theValueESet;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public AttributeDefinitionReal getDefinition() {
		if (definition != null && definition.eIsProxy()) {
			InternalEObject oldDefinition = (InternalEObject) definition;
			definition = (AttributeDefinitionReal) eResolveProxy(oldDefinition);
			if (definition != oldDefinition) {
				if (eNotificationRequired())
					eNotify(new ENotificationImpl(this, Notification.RESOLVE, ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION, oldDefinition,
							definition));
			}
		}
		return definition;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public AttributeDefinitionReal basicGetDefinition() {
		return definition;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void setDefinition(AttributeDefinitionReal newDefinition) {
		AttributeDefinitionReal oldDefinition = definition;
		definition = newDefinition;
		boolean oldDefinitionESet = definitionESet;
		definitionESet = true;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION, oldDefinition, definition,
					!oldDefinitionESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public void unsetDefinition() {
		AttributeDefinitionReal oldDefinition = definition;
		boolean oldDefinitionESet = definitionESet;
		definition = null;
		definitionESet = false;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.UNSET, ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION, oldDefinition, null,
					oldDefinitionESet));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	public boolean isSetDefinition() {
		return definitionESet;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * 
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE:
			return getTheValue();
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION:
			if (resolve)
				return getDefinition();
			return basicGetDefinition();
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
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE:
			setTheValue((Double) newValue);
			return;
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION:
			setDefinition((AttributeDefinitionReal) newValue);
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
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE:
			unsetTheValue();
			return;
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION:
			unsetDefinition();
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
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__THE_VALUE:
			return isSetTheValue();
		case ReqIF10Package.ATTRIBUTE_VALUE_REAL__DEFINITION:
			return isSetDefinition();
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
		result.append(" (theValue: "); //$NON-NLS-1$
		if (theValueESet)
			result.append(theValue);
		else
			result.append("<unset>"); //$NON-NLS-1$
		result.append(')');
		return result.toString();
	}

} // AttributeValueRealImpl
