package org.powermock.modules.junit4.legacy.internal.impl.testcaseworkaround;

import junit.framework.TestCase;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.internal.runners.TestClassMethodsRunner;
import org.junit.internal.runners.TestMethodRunner;
import org.junit.runner.notification.RunNotifier;
import org.powermock.core.spi.PowerMockTestListener;
import org.powermock.reflect.Whitebox;
import org.powermock.tests.utils.PowerMockTestNotifier;
import org.powermock.tests.utils.impl.PowerMockTestNotifierImpl;
import org.powermock.tests.utils.impl.StaticConstructorSuppressExtractorImpl;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.LinkedList;
import java.util.List;

/**
 * Since {@link TestClassMethodsRunner} creates a new instance of
 * TestInterceptor in its constructor we need to manually lookup the additional
 * methods that should be added when extending from <code>TestCase</code>.
 */
public class PowerMockJUnit4LegacyTestClassMethodsRunner extends TestClassMethodsRunner {

	private final PowerMockTestNotifier powerMockTestNotifier;

	@SuppressWarnings("unchecked")
	public PowerMockJUnit4LegacyTestClassMethodsRunner(Class<?> klass, PowerMockTestListener[] powerMockTestListeners) {
		super(klass);
		this.powerMockTestNotifier = new PowerMockTestNotifierImpl(powerMockTestListeners);
		List<Method> testMethods = (List<Method>) Whitebox.getInternalState(this, "fTestMethods", TestClassMethodsRunner.class);
		testMethods.addAll(getAdditionalTestMethods(klass));
	}

	private List<Method> getAdditionalTestMethods(Class<?> klass) {
		List<Method> additionalMethods = new LinkedList<Method>();
		if (klass != null && klass.getSuperclass().equals(TestCase.class)) {
			/*
			 * We now know that we need to add additional test methods because
			 * JUnit4 ignores public methods with no @Test annotation when
			 * extending from TestCase.
			 */
			Method[] methods = klass.getMethods();
			for (Method method : methods) {
				if (isAdditionalTestMethod(method)) {
					additionalMethods.add(method);
				}
			}
		}
		return additionalMethods;

	}

	private boolean isAdditionalTestMethod(Method method) {
		if (!method.isAnnotationPresent(Ignore.class) && method.getName().startsWith("test") && Modifier.isPublic(method.getModifiers())
				&& method.getReturnType().equals(Void.TYPE) && method.getAnnotation(Test.class) == null) {
			return true;
		}
		return false;
	}

	@Override
	protected TestMethodRunner createMethodRunner(Object test, Method method, RunNotifier notifier) {
		return new PowerMockJUnit4LegacyTestMethodRunner(test, method, notifier, methodDescription(method), powerMockTestNotifier);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void run(RunNotifier notifier) {
		final List<Method> methods = (List<Method>) Whitebox.getInternalState(this, "fTestMethods");
		if (methods.isEmpty())
			notifier.testAborted(getDescription(), new Exception("No runnable methods"));
		for (Method method : methods) {
			final StaticConstructorSuppressExtractorImpl staticConstructorSuppressExtractorImpl = new StaticConstructorSuppressExtractorImpl();
			Class<?> testType = getTestClass();
			final ClassLoader thisClassLoader = getClass().getClassLoader();
			if (!thisClassLoader.equals(testType.getClassLoader())) {
				/*
				 * The test is loaded from another classloader, this means that
				 * we cannot get the correct annotations if we don't load the
				 * class from the correct class loader
				 */
				try {
					testType = thisClassLoader.loadClass(testType.getName());
				} catch (ClassNotFoundException e) {
					// This should never happen
					throw new RuntimeException("Internal error in PowerMock", e);
				}
			}
			if (staticConstructorSuppressExtractorImpl.getTestClasses(method) == null) {
				staticConstructorSuppressExtractorImpl.getTestClasses(testType);
			}

			invokeTestMethod(method, notifier);
		}
	}

}
