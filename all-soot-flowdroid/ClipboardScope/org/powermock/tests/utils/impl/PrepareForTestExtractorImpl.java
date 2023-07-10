/*
 * Copyright 2011 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.powermock.tests.utils.impl;

import org.powermock.core.IndicateReloadClass;
import org.powermock.core.classloader.annotations.PrepareForTest;
import org.powermock.core.classloader.annotations.PrepareOnlyThisForTest;
import org.powermock.tests.utils.TestClassesExtractor;

import java.lang.reflect.AnnotatedElement;
import java.lang.reflect.Method;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Implementation of the {@link TestClassesExtractor} interface that extract
 * classes from the {@link PrepareForTest} or {@link PrepareOnlyThisForTest}
 * annotations. It also adds the test case to the array of classes that should
 * be modified.
 * 
 */
public class PrepareForTestExtractorImpl extends AbstractTestClassExtractor {

    /**
     * {@inheritDoc}
     */
    @Override
    protected String[] getClassesToModify(AnnotatedElement element) {
        Set<String> all = new LinkedHashSet<String>();
        addTestCase(all, element);
        PrepareForTest prepareForTestAnnotation = element.getAnnotation(PrepareForTest.class);
        PrepareOnlyThisForTest prepareOnlyThisForTestAnnotation = element.getAnnotation(PrepareOnlyThisForTest.class);
        final boolean prepareForTestAnnotationPresent = prepareForTestAnnotation != null;
        final boolean prepareOnlyThisForTestAnnotationPresent = prepareOnlyThisForTestAnnotation != null;

        if (!prepareForTestAnnotationPresent && !prepareOnlyThisForTestAnnotationPresent) {
            return null;
        }

        if (prepareForTestAnnotationPresent) {
            final Class<?>[] classesToMock = prepareForTestAnnotation.value();
            for (Class<?> classToMock : classesToMock) {
                if (!classToMock.equals(IndicateReloadClass.class)) {
                    addClassHierarchy(all, classToMock);
                }
            }

            addFullyQualifiedNames(all, prepareForTestAnnotation);
        }

        if (prepareOnlyThisForTestAnnotationPresent) {
            final Class<?>[] classesToMock = prepareOnlyThisForTestAnnotation.value();
            for (Class<?> classToMock : classesToMock) {
                if (!classToMock.equals(IndicateReloadClass.class)) {
                    all.add(classToMock.getName());
                }
            }

            addFullyQualifiedNames(all, prepareOnlyThisForTestAnnotation);
        }

        return all.toArray(new String[0]);

    }

    private void addTestCase(Set<String> all, AnnotatedElement element) {
        Class<?> testClass = null;
        if (element instanceof Class<?>) {
            testClass = (Class<?>) element;
        } else if (element instanceof Method) {
            testClass = ((Method) element).getDeclaringClass();
        }
        addClassHierarchy(all, testClass);
    }

    private void addFullyQualifiedNames(Set<String> all, PrepareForTest annotation) {
        String[] fullyQualifiedNames = annotation.fullyQualifiedNames();
        addFullyQualifiedNames(all, fullyQualifiedNames);
    }

    private void addFullyQualifiedNames(Set<String> all, PrepareOnlyThisForTest annotation) {
        String[] fullyQualifiedNames = annotation.fullyQualifiedNames();
        addFullyQualifiedNames(all, fullyQualifiedNames);
    }

    private void addFullyQualifiedNames(Set<String> all, String[] fullyQualifiedNames) {
        for (String string : fullyQualifiedNames) {
            if (!"".equals(string)) {
                all.add(string);
            }
        }
    }

    private void addClassHierarchy(Set<String> all, Class<?> classToMock) {
        while (classToMock != null && !classToMock.equals(Object.class)) {
            addInnerClassesAndInterfaces(all, classToMock);
            all.add(classToMock.getName());
            classToMock = classToMock.getSuperclass();
        }
    }

    private void addInnerClassesAndInterfaces(Set<String> all, Class<?> classToMock) {
        Class<?>[] declaredClasses = classToMock.getDeclaredClasses();
        for (Class<?> innerClass : declaredClasses) {
            all.add(innerClass.getName());
        }
    }
}
