package com.example.finalhand1;


import android.content.Context;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.util.Log;
import android.view.Window;
import android.view.WindowManager;

import static android.content.Context.SENSOR_SERVICE;
import static com.example.finalhand1.RecHands.myTAG;

public class BrightnessAdapter implements SensorEventListener {
    private Context mContext;
    private SensorManager sensorManager;
    private Window mWindow;

    public BrightnessAdapter(Context fContext, Window fWindow) {
        this.mContext = fContext;
        this.mWindow=fWindow;
        this.sensorManager=(SensorManager)mContext.getSystemService(SENSOR_SERVICE);
    }

    /**
     * 对于使用的光纤传感器的注册：需要获得使用的相关权限
     */
    public void regist(){
        if(sensorManager!=null){
            sensorManager.registerListener(this,sensorManager.getDefaultSensor(Sensor.TYPE_LIGHT),SensorManager.SENSOR_DELAY_GAME);
        }
    }

    public void unRegist(){
        if(sensorManager!=null){
            sensorManager.unregisterListener(this,sensorManager.getDefaultSensor(Sensor.TYPE_LIGHT));
        }
    }


    @Override
    public void onSensorChanged(SensorEvent event) {
        float[] values = event.values;
//        Log.d(myTAG, "onSensorChanged: 当前光纤传感器获得的对应的光线数值的情况"+values[0]);
        //传感器类型
        int sensorType = event.sensor.getType();
        switch (sensorType){
            case Sensor.TYPE_LIGHT:
                //对于光线传感器的变化，进行相关的亮度调节
                //获取窗口管理属性
                WindowManager.LayoutParams lp =mWindow.getAttributes();
                //计算屏幕亮度
//                lp.screenBrightness = Float.valueOf(values[0])*(1f/255f);
                lp.screenBrightness = Float.valueOf(values[0])*(1f/350f);

                //参数设置
                mWindow.setAttributes(lp);
                break;
            default:break;
        }
    }

    @Override
    public void onAccuracyChanged(Sensor sensor, int accuracy) {

    }
}