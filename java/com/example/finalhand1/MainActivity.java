package com.example.finalhand1;


import static com.example.finalhand1.RecHands.myTAG;
import static java.lang.Math.max;
import static java.lang.Math.min;
import android.Manifest;

import android.app.Instrumentation;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.PackageManager.NameNotFoundException;
import android.graphics.SurfaceTexture;
import android.hardware.SensorEvent;
import android.os.Bundle;

import androidx.annotation.NonNull;
import androidx.appcompat.app.AppCompatActivity;
import androidx.core.app.ActivityCompat;
import androidx.core.app.NotificationManagerCompat;
import androidx.core.content.ContextCompat;
import androidx.preference.PreferenceManager;
import androidx.viewpager2.adapter.FragmentStateAdapter;
import androidx.viewpager2.widget.ViewPager2;

import android.os.Handler;
import android.os.Message;
import android.os.SystemClock;
import android.provider.Settings;
import android.util.DisplayMetrics;
import android.util.Log;
import android.util.Size;
import android.view.MotionEvent;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.view.WindowManager;
import android.widget.AdapterView;
import android.widget.LinearLayout;
import android.widget.ListView;
import android.widget.ProgressBar;
import android.widget.TextView;


import com.example.finalhand1.DTW.pointHistory;
//import com.example.finalhand1.MapControl.MapControl;
import com.example.finalhand1.MapControl.MapControl;
import com.example.finalhand1.mainmenuUI.MainMenu;
import com.example.finalhand1.mainmenuUI.MenuAdapter;
import com.google.mediapipe.formats.proto.LandmarkProto;
import com.google.mediapipe.formats.proto.LandmarkProto.NormalizedLandmarkList;
import com.google.mediapipe.components.CameraHelper;
import com.google.mediapipe.components.CameraXPreviewHelper;
import com.google.mediapipe.components.ExternalTextureConverter;
import com.google.mediapipe.components.FrameProcessor;
import com.google.mediapipe.components.PermissionHelper;
import com.google.mediapipe.framework.AndroidAssetUtil;
import com.google.mediapipe.framework.AndroidPacketCreator;
import com.google.mediapipe.framework.PacketGetter;
import com.google.mediapipe.framework.Packet;
import com.google.mediapipe.glutil.EglManager;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * Main activity of MediaPipe example apps.
 */
public class MainActivity extends AppCompatActivity {
    private static final String BINARY_GRAPH_NAME = "hand_tracking_mobile_gpu.binarypb";
    private static final String INPUT_VIDEO_STREAM_NAME = "input_video";
    private static final String OUTPUT_VIDEO_STREAM_NAME = "output_video";
    private static final String OUTPUT_LANDMARKS_STREAM_NAME = "hand_landmarks";
    private static final String OUTPUT_DETECTIONS_STREAM_NAME = "palm_detections";
    private static final String INPUT_NUM_HANDS_SIDE_PACKET_NAME = "num_hands";
    private static final int NUM_HANDS = 1;
    private static final int numThreads = 1;
    // private static final CameraHelper.CameraFacing CAMERA_FACING = CameraHelper.CameraFacing.FRONT;
    // Flips the camera-preview frames vertically before sending them into FrameProcessor to be
    // processed in a MediaPipe graph, and flips the processed frames back when they are displayed.
    // This is needed because OpenGL represents images assuming the image origin is at the bottom-left
    // corner, whereas MediaPipe in general assumes the image origin is at top-left.
    private static final boolean FLIP_FRAMES_VERTICALLY = true;

    static {
        // Load all native libraries needed by the app.
        System.loadLibrary("mediapipe_jni");
        System.loadLibrary("opencv_java3");
    }

    // {@link SurfaceTexture} where the camera-preview frames can be accessed.
    private SurfaceTexture previewFrameTexture;
    // {@link SurfaceView} that displays the camera-preview frames processed by a MediaPipe graph.
    private SurfaceView previewDisplayView;
    // Creates and manages an {@link EGLContext}.
    private EglManager eglManager;
    // Sends camera-preview frames into a MediaPipe graph for processing, and displays the processed
    // frames onto a {@link Surface}.
    private FrameProcessor processor;
    // Converts the GL_TEXTURE_EXTERNAL_OES texture from Android camera into a regular texture to be
    // consumed by {@link FrameProcessor} and the underlying MediaPipe graph.
    private ExternalTextureConverter converter;
    // ApplicationInfo for retrieving metadata defined in the manifest.
    private ApplicationInfo applicationInfo;
    // Handles camera access via the {@link CameraX} Jetpack support library.
    private CameraXPreviewHelper cameraHelper;
    private long lastProcessingTimeMs;

    private ViewPager2 viewPager;
    private FragmentStateAdapter pagerAdapter;
    private LinearLayout ll_image_room, ll_photo1_room, ll_photo2_room;
    //创建控制窗口亮度的回调(实现相关信息的传递)
    private Handler windowHandler;

    private int image_width = 720;
    private int image_height = 1280;

    long timestampbefor = -1;
    long timespend = 0;
    boolean flag = true;

    int k = 10;   //the number frame to do a act
    int numm = 0; //the total frame hand detection
    Float preVex = Float.valueOf(-1); // the prior hand x position
    Float handDistance = Float.valueOf(0);
    String currentView = "image_room";  //当前显示界面名称，初始为图像库选择界面
    //    String selectImageRoom = "anime";   //当前选中图库名称，初始为anime
    List<Integer> urlList_city = new ArrayList<>();
    List<Integer> urlList_universe = new ArrayList<>();
    private int menu1 = 0;

    private List<MainMenu> fruitList = new ArrayList<>();
    /**
     DTW进行动态手势识别中，使用到的手指关键点
     使用static静态变量，保证在退出活动操控后，训练序列（作为模板）数据仍能够被保留下来
     */
    // 选择地图放大手势
    public static pointHistory num8;
    public static pointHistory num7;
    public static pointHistory num6;
    public static pointHistory num4;
    public static pointHistory num3;
    // 选择地图缩小手势
    public static pointHistory num80;
    public static pointHistory num70;
    public static pointHistory num60;
    public static pointHistory num40;
    public static pointHistory num30;
//    AudioManager am = (AudioManager)context.getSystemService(Context.AUDIO_SERVICE);

    /*
    调用窗口亮度调节的类，实现光线传感器对应的亮度自动调节
     */
    BrightnessAdapter myAPP_BrightnessAdapter;
    private SensorEvent myApp_Light_event;
    ProgressBar progressBar;

    private int[] click_times=new int[3];// 针对3个按钮的listview
    private int click_total_times=25;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(getContentViewLayoutResId());


        //主界面的菜单
        initFruits();
        MenuAdapter adapter = new MenuAdapter(this, R.layout.main_menu_ui_item, fruitList);
        ListView listView = (ListView) findViewById(R.id.list_view);
        listView.setAdapter(adapter);
        // 3.9.2023 实现listview按钮的长按跳转
        listView.setOnItemLongClickListener(new AdapterView.OnItemLongClickListener() {
            @Override
            public boolean onItemLongClick(AdapterView<?> adapterView, View view, int position, long l) {
                switch (position){
                    case 0:
                        doAction("one");
                        break;
                    case 1:
                        doAction("TWO");
                        break;
                    case 2:
                        doAction("FINISHSIGN");
                        break;
                }
                return true;
            }
        });

        // listview点击跳转-针对空中手势操控
        listView.setOnItemClickListener(new AdapterView.OnItemClickListener() {
            @Override
            public void onItemClick(AdapterView<?> parent, View view, int position, long id) {
                switch (position) {
                    case 0:
                    {
                        click_times[position]++;
                        // 避免点错按键，清空其他按键次数
                        for (int i=0;i<click_times.length;i++)
                        {
                            if(i==position)
                                continue;
                            else
                                click_times[i]=0;
                        }
                        Log.d(myTAG, "onItemClick: "+click_times);
                        if(click_times[position]==click_total_times)
                        {
                            doAction("one");
                            click_times[position]=0;
                        }
                        break;
                    }
                    case 1:
                    {
                        click_times[position]++;
                        // 避免点错按键，清空其他按键次数
                        for (int i=0;i<click_times.length;i++)
                        {
                            if(i==position)
                                continue;
                            else
                                click_times[i]=0;
                        }
                        Log.d(myTAG, "onItemClick: "+click_times);
                        if(click_times[position]==click_total_times)
                        {
                            doAction("TWO");
                            click_times[position]=0;
                        }
                        break;
                    }
                    case 2:
                    {
                        click_times[position]++;
                        // 避免点错按键，清空其他按键次数
                        for (int i=0;i<click_times.length;i++)
                        {
                            if(i==position)
                                continue;
                            else
                                click_times[i]=0;
                        }
                        Log.d(myTAG, "onItemClick: "+click_times);
                        if(click_times[position]==click_total_times)
                        {
                            doAction("FINISHSIGN");
                            click_times[position]=0;
                        }
                        break;
                    }
                }
            }
        });



        /*
         * 关键点对象的初始化DTW
         */
        num8=new pointHistory();
        num7=new pointHistory();
        num6=new pointHistory();
        num4=new pointHistory();
        num3=new pointHistory();
        // 地图缩小手势
        num80=new pointHistory();
        num70=new pointHistory();
        num60=new pointHistory();
        num40=new pointHistory();
        num30=new pointHistory();

        //防止多次识别
        menu1 = 0;

        // Instantiate a ViewPager2 and a PagerAdapter.
        viewPager = findViewById(R.id.pager);

        /*
        对于窗口相关参数调节的回调的相关声明
            对于亮度调节
         */
        windowHandler=new Handler(new Handler.Callback() {
            @Override
            public boolean handleMessage(@NonNull Message message) {
                //获得回调传递的信息
                Bundle bundle=message.getData();
                //获得回调中相应关键字的内容
                Integer action=(Integer) bundle.get("window");
                //执行相关动作
                setAppScreenBrightness(action);
                return false;
            }
        });

        try {
            applicationInfo =
                    getPackageManager().getApplicationInfo(getPackageName(), PackageManager.GET_META_DATA);
        } catch (NameNotFoundException e) {
            Log.e(myTAG, "Cannot find application info: " + e);
        }

        previewDisplayView = new SurfaceView(this);
        setupPreviewDisplayView();

        // Initialize asset manager so that MediaPipe native libraries can access the app assets, e.g.,
        // binary graphs.
        AndroidAssetUtil.initializeNativeAssetManager(this);
        eglManager = new EglManager(null);
        processor =
                new FrameProcessor(
                        this,
                        eglManager.getNativeContext(),
                        BINARY_GRAPH_NAME,
                        INPUT_VIDEO_STREAM_NAME,
                        OUTPUT_VIDEO_STREAM_NAME);
        processor
                .getVideoSurfaceOutput()
                .setFlipY(FLIP_FRAMES_VERTICALLY);

        PermissionHelper.checkAndRequestCameraPermissions(MainActivity.this);
        AndroidPacketCreator packetCreator = processor.getPacketCreator();
        Map<String, Packet> inputSidePackets = new HashMap<>();
        inputSidePackets.put(INPUT_NUM_HANDS_SIDE_PACKET_NAME, packetCreator.createInt32(NUM_HANDS));
        processor.setInputSidePackets(inputSidePackets);

        //设置进入每个活动的延迟，避免一识别到就进入活动
        first_activity = 0;
        second_activity = 0;
        game_acitivty = 0;
        flag_activity = -1;

        int len_of_array_to_count_activity = array_to_count_activity.length;
        for (int i = 0; i < len_of_array_to_count_activity; i++) {
            array_to_count_activity[i] = 0;
        }

        /*
        使用光线传感器实现亮度的调节
        8.20 成功
         */
        myAPP_BrightnessAdapter =new BrightnessAdapter(getApplicationContext(),getWindow());
        myAPP_BrightnessAdapter.regist();

        // 调节进度条
        progressBar = (ProgressBar) findViewById(R.id.progress_bar_main);
        change_the_bar(0);

        // To show verbose logging, run:
        // adb shell setprop log.tag.MainActivity VERBOSE
        processor.addPacketCallback(
                OUTPUT_LANDMARKS_STREAM_NAME,
                (packet) -> {
//                    Log.v(myTAG, "Received multi-hand landmarks packet.");
                    List<NormalizedLandmarkList> multiHandLandmarks =
                            PacketGetter.getProtoVector(packet, NormalizedLandmarkList.parser());

//                    HandleTheHands(multiHandLandmarks);
                    // : 2023/3/7 空中手指坐标处理
                    finger_pointer_show(multiHandLandmarks);
//                    if (juTheback(packet, multiHandLandmarks)) {
//                        finish();
//                    }
                });
    }


    @Override
    public void onRequestPermissionsResult(
            int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        PermissionHelper.onRequestPermissionsResult(requestCode, permissions, grantResults);
    }
    //    修改进度条

    private void change_the_bar(int change_num) {
        progressBar.setProgress(max(0, min(change_num * 4, 100)));
    }

    //初始化菜单

    private void initFruits() {
        MainMenu volControl = new MainMenu("地图控制", R.drawable.one);
        fruitList.add(volControl);
        MainMenu login = new MainMenu("用户手势录入", R.drawable.two);
        fruitList.add(login);
        MainMenu finish_app = new MainMenu("退出", R.drawable.finish_sign);
        fruitList.add(finish_app);
    }
    int first_activity, second_activity, game_acitivty = 0, finish_app = 0;
    int flag_activity = -1;

    private int array_to_count_activity[] = new int[20];

    HashMap string_to_num_map = new HashMap();
    //根据不同的手势跳转到不同的菜单

    /**
     * 空中手势手指的坐标
     * @param multiHandLandmarks
     */
    private void finger_pointer_show(List<NormalizedLandmarkList> multiHandLandmarks){
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
        //获得手腕点的坐标
        Float pointer_x = landmarks.getLandmark(8).getX();// 获得食指指尖x
        Float pointer_y=landmarks.getLandmark(8).getY();// 获得食指指尖y
        // 当前视频在屏幕上的大小 按照相对于父容器的情况进行计算
        TextView vedio_load_size=findViewById(R.id.no_camera_access_view);
        // 直接获得当前屏幕的大小
        DisplayMetrics displayMetrics = new DisplayMetrics();
        getWindowManager().getDefaultDisplay().getMetrics(displayMetrics);
        int vedio_width=vedio_load_size.getWidth();// 获得的宽度是1080，结果没有误差
        int vedio_height=displayMetrics.heightPixels;
        // 归一化坐标恢复
        pointer_x=pointer_x*vedio_width;
        pointer_y=pointer_y*vedio_height;
        Log.d(myTAG, "finger_pointer_show: "+"point_x:"+pointer_x.toString()+" point_y:"+pointer_y.toString());
        Float finalPointer_y = pointer_y;
        Float finalPointer_x = pointer_x;
        // 使用Instrumentation以及对应的线程实现手指动作的仿真
        new Thread(new Runnable() {
            @Override
            public void run() {
                // Instrumentation作用是编写自动化测试用例，可以模拟用户的操作行为，从而测试应用程序的功能和可靠性。由于本质是一种用于监控应用程序运行状态的工具，需要单独开辟一个线程
                Instrumentation mInst = new Instrumentation();
                try {
                    mInst.sendPointerSync(MotionEvent.obtain(SystemClock.uptimeMillis(), SystemClock.uptimeMillis(),
                            MotionEvent.ACTION_DOWN, finalPointer_x, finalPointer_y, 0));
                    mInst.sendPointerSync(MotionEvent.obtain(SystemClock.uptimeMillis(), SystemClock.uptimeMillis(),
                            MotionEvent.ACTION_UP, finalPointer_x, finalPointer_y, 0));
                }catch (SecurityException ignored){}
            }
        }).start();
    }

    private void HandleTheHands(List<NormalizedLandmarkList> multiHandLandmarks) {
        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
        // : 9/8/2022 实现手掌识别范围的限制
        /*
        实现思路：获得控件上下边沿在y方向上的位置，由于在不同手势的时候，手指不一定是手部相对位置最高的，因此选择通过限制手掌的位置实现识别区域的判定
         */
        //获得手腕点的坐标
        Float y2 = landmarks.getLandmark(9).getY();// 获得中指根部的纵坐标情况
        Float yy=landmarks.getLandmark(0).getY();
        // 当前视频在屏幕上的大小 按照相对于父容器的情况进行计算
        TextView vedio_load_size=findViewById(R.id.no_camera_access_view);
        int vedio_bottom=vedio_load_size.getBottom();
        int vedio_top=vedio_load_size.getTop();
        int vedio_height=vedio_bottom-vedio_top;
        //获得识别区域控件在屏幕上的坐标
        TextView rec_zone=findViewById(R.id.rec_zone);
        int rec_zone_bottom=rec_zone.getBottom();
        int rec_zone_top=rec_zone.getTop();
        if(!(yy*vedio_height>rec_zone_top&&yy*vedio_height<rec_zone_bottom&&y2*vedio_height>rec_zone_top&&y2*vedio_height<rec_zone_bottom)){
//            Log.d(myTAG, "当前的手掌不在识别范围内");
            return;
        }
//        int[] rec_zone_locate=new int[2];
//        Log.d(myTAG, "控件四周的位置情况: 下方="+rec_zone.getBottom()+" 上方="+rec_zone.getTop());
//        rec_zone.getLocationOnScreen(rec_zone_locate);// 获得控件在屏幕上的坐标情况
//        Log.d(myTAG, "控件的位置：x="+rec_zone_locate[0]+" y="+rec_zone_locate[1]);
        int upper_limit = 25;
        string_to_num_map.put("one", 1);
        string_to_num_map.put("TWO", 2);
        string_to_num_map.put("THREE", 3);
        string_to_num_map.put("FOUR", 4);
        string_to_num_map.put("FIVE", 5);
//        string_to_num_map.put("SIX", 6);
        string_to_num_map.put("FINISHSIGN", 6);
        if (string_to_num_map.containsKey(title)) {
            int want_the_num = (Integer) string_to_num_map.get(title);
            if (flag_activity == -1 || flag_activity == want_the_num) {
                array_to_count_activity[want_the_num]++;
                change_the_bar(array_to_count_activity[want_the_num]);
            } else {
                flag_activity = want_the_num;
                array_to_count_activity[want_the_num] = 0;
                change_the_bar(0);
            }
            for (int i = 0; i < array_to_count_activity.length; i++) {
                if (i == want_the_num)
                    continue;
                array_to_count_activity[i] = 0;
            }
//            Log.d("titleis", title + array_to_count_activity[want_the_num]);
            if (array_to_count_activity[want_the_num] == upper_limit) {
                doAction(title);
            }
//            send_integer2bundle(255);
        } else {
            for (int i = 0; i < array_to_count_activity.length; i++) {
                array_to_count_activity[i] = 0;
            }
            flag_activity = -1;
            change_the_bar(0);
            /*
            降低当前屏幕的亮度并且显示当前屏幕的亮度
             */
//            send_integer2bundle(50);
            int now_APPBrightness=getScreenBrightness(getApplicationContext());
//            Log.d(myTAG, "HandleTheHands: 当前屏幕的亮度"+now_APPBrightness);
        }
    }

    /**
     * 构造回调的相关处理函数
     * @param action
     */
    private void send_integer2bundle(int action) {
        Bundle bundle=new Bundle();
        bundle.putInt("window",action);//回调中放入需要传递的key和整数内容
        Message message=new Message();
        message.setData(bundle);
        windowHandler.sendMessage(message);
    }

    /**
     * 设置软件亮度调高的函数
     * @param i
     */
    private void setAppScreenBrightness(int i) {
        Window window=getWindow();
        WindowManager.LayoutParams lp=window.getAttributes();//获得当前窗口的参数
        lp.screenBrightness=i/255.0f;
        window.setAttributes(lp);
    }

    /**
     * 获得软件当前的亮度情况
     * @param context
     * @return 返回当前系统的亮度情况（使用的是整数）
     */
    private int getScreenBrightness(Context context) {
        ContentResolver contentResolver=context.getContentResolver();
        int defVal=125;
        return Settings.System.getInt(contentResolver,Settings.System.SCREEN_BRIGHTNESS,defVal);
    }


    private boolean juTheback(Packet packet, List<NormalizedLandmarkList> multiHandLandmarks) {
        boolean wantback = false;
        //获取当前数据包时间戳
        long timestamp = packet.getTimestamp();
        //将第一个数据包时间戳记录
        if (timestampbefor == -1) {
            timestampbefor = timestamp;
        }
        //获取两个数据包时间戳之间的差值
        timespend = timestamp - timestampbefor;
        //记录当前数据包时间戳，以便计算下一时间间隔
        timestampbefor = timestamp;
//        Log.v(myTAG, "TS:" + timespend + "");
        //经实验，间隔200000比较合理
        if (timespend > 200000) {
            //标志位为ture，允许检测手势
            flag = true;
            //将之前的手势信息重置，重新检测
            preVex = Float.valueOf(-1);
            handDistance = Float.valueOf(0);
        }
        Float Vex;  //当前手指X位置坐标

        if (multiHandLandmarks.isEmpty()) {
            Log.v("empty", preVex.toString());
        }
        for (NormalizedLandmarkList landmarks : multiHandLandmarks) {
            //以食指指根关节x位置坐标 进行检测
            Vex = landmarks.getLandmark(5).getX();
            //若为首次出现手
            if (preVex.equals(Float.valueOf(-1))) {
                preVex = Vex;
            }
            //判断两帧之间手的位置距离，避免出现手位置闪烁现象，
            //处理后的手的x坐标范围是【0,1】，经实验，间隔0.7以内可判定为正常移动
            if (Math.abs(preVex - Vex) < 0.7 && Math.abs(preVex - Vex) > 0.4) {
                //获取两帧之间手的位置距离，并进行累加操作
                handDistance += (preVex - Vex);
            }
//            Log.v("handDistance",handDistance + "");
            numm++;     //计算已经获取帧数
            if (handDistance < -0.8) {
                //向右滑动
                Log.v("Right", "Right");
                handDistance = Float.valueOf(0);
                preVex = Float.valueOf(-1);
                numm = 0;
                wantback = true;
            }
        }
        return wantback;
    }

    private void doAction(String action) {
        // 当识别到手势时，跳转到对应的activity
        if ("one".equals(action) && menu1 == 0) {
            // 设置 音乐控制 的跳转
            Intent intent = new Intent(this, MapControl.class);
            startActivity(intent);
            menu1 = 1;
        } else if ("TWO".equals(action) && menu1 == 0) {
            // : 2021/11/24
            Intent intent = new Intent(this, login.class);
            startActivity(intent);
            menu1 = 1;
        }else if ("FINISHSIGN".equals(action)||"FINISHSIGN".equals(action)) {
            finish();
        }
    }
    // Used to obtain the content view for this application. If you are extending this class, and
    // have a custom layout, override this method and return the custom layout.
    // 获得应用对应的view 如果继承当前类或者是对类进行了自定义，需要返回自定义的view文件
    protected int getContentViewLayoutResId() {
        return R.layout.main_in_change1;
    }

    @Override
    protected void onResume() {
        menu1 = 0;
        //设置进入每个活动的延迟，避免一识别到就进入活动
        first_activity = 0;
        second_activity = 0;
        game_acitivty = 0;
        flag_activity = -1;
        change_the_bar(0);
        try {
            super.onResume();
            converter =
                    new ExternalTextureConverter(
                            eglManager.getContext(), 2);
            converter.setFlipY(FLIP_FRAMES_VERTICALLY);
            converter.setConsumer(processor);
            /*
            动态权限的授予
             */
            if (PermissionHelper.cameraPermissionsGranted(this)) {
                startCamera();
            }//相机的权限被集成在jar包中
//            //如果没有授予READ_PHONE_STATE权限 电话权限的授予
//            if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ANSWER_PHONE_CALLS) != PackageManager.PERMISSION_GRANTED){
//                //跳转授权界面
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ANSWER_PHONE_CALLS}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ACCESS_COARSE_LOCATION}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ACCESS_FINE_LOCATION}, 1);
//            }
//            else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_WIFI_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ACCESS_WIFI_STATE}, 1);
//            }
//            else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.WRITE_EXTERNAL_STORAGE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.WRITE_EXTERNAL_STORAGE}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_NETWORK_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ACCESS_NETWORK_STATE}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.CHANGE_WIFI_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.CHANGE_WIFI_STATE}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.INTERNET) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.INTERNET}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_LOCATION_EXTRA_COMMANDS) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.ACCESS_LOCATION_EXTRA_COMMANDS}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.FOREGROUND_SERVICE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{ Manifest.permission.FOREGROUND_SERVICE}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.ACCESS_BACKGROUND_LOCATION) != PackageManager.PERMISSION_GRANTED) {//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{Manifest.permission.ACCESS_BACKGROUND_LOCATION}, 1);
//            }else if(ContextCompat.checkSelfPermission(this, Manifest.
//                    permission.BIND_NOTIFICATION_LISTENER_SERVICE) != PackageManager.PERMISSION_GRANTED) {//网络定位的权限的获取
//                ActivityCompat.requestPermissions(this, new
//                        String[]{Manifest.permission.BIND_NOTIFICATION_LISTENER_SERVICE}, 1);
//            }
//            //判断通知栏监听的权限是否授予
//            else if(!isNLServiceEnabled()) {
//                //动态权限授予
//                Intent intent = new Intent("android.settings.ACTION_NOTIFICATION_LISTENER_SETTINGS");
//                startActivityForResult(intent, REQUEST_CODE);//通过将激活码传递 实现按钮功能的响应
//            }else if(isNLServiceEnabled()){
//                Log.d(myTAG, "MainActivity onReusume:通知服务已经开启!");
//            }
        } catch (Exception e) {
        }
    }
    private static final int REQUEST_CODE = 9527;

    /**
     * 是否启用通知监听服务
     *
     * @return
     */
    public boolean isNLServiceEnabled() {
        Set<String> packageNames = NotificationManagerCompat.getEnabledListenerPackages(this);
        if (packageNames.contains(getPackageName())) {
            return true;
        }
        return false;
    }

    @Override
    protected void onPause() {
        super.onPause();
        converter.close();

        // Hide preview display until we re-open the camera again.
        previewDisplayView.setVisibility(View.GONE);
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        try {
            System.exit(0);
        } catch (Exception e) {
            System.exit(1);
        }
    }

    protected void onCameraStarted(SurfaceTexture surfaceTexture) {
        previewFrameTexture = surfaceTexture;
        // Make the display view visible to start showing the preview. This triggers the
        // SurfaceHolder.Callback added to (the holder of) previewDisplayView.
        previewDisplayView.setVisibility(View.VISIBLE);
    }

    protected Size cameraTargetResolution() {
        return null; // No preference and let the camera (helper) decide.
    }

    public void startCamera() {
        cameraHelper = new CameraXPreviewHelper();
        cameraHelper.setOnCameraStartedListener(
                surfaceTexture -> {
                    onCameraStarted(surfaceTexture);
                });
        CameraHelper.CameraFacing cameraFacing = CameraHelper.CameraFacing.FRONT;
        cameraHelper.startCamera(
                this, cameraFacing, /*unusedSurfaceTexture=*/ null, cameraTargetResolution());
    }

    protected Size computeViewSize(int width, int height) {
        return new Size(width, height);
    }

    protected void onPreviewDisplaySurfaceChanged(
            SurfaceHolder holder, int format, int width, int height) {
        // (Re-)Compute the ideal size of the camera-preview display (the area that the
        // camera-preview frames get rendered onto, potentially with scaling and rotation)
        // based on the size of the SurfaceView that contains the display.
        Size viewSize = computeViewSize(width, height);
        Size displaySize = cameraHelper.computeDisplaySizeFromViewSize(viewSize);
        boolean isCameraRotated = cameraHelper.isCameraRotated();

        // Connect the converter to the camera-preview frames as its input (via
        // previewFrameTexture), and configure the output width and height as the computed
        // display size.
        image_width = isCameraRotated ? displaySize.getHeight() : displaySize.getWidth();
        image_height = isCameraRotated ? displaySize.getWidth() : displaySize.getHeight();

        converter.setSurfaceTextureAndAttachToGLContext(
                previewFrameTexture,
                isCameraRotated ? displaySize.getHeight() : displaySize.getWidth(),
                isCameraRotated ? displaySize.getWidth() : displaySize.getHeight());
        // 解决刚开始打开应用黑屏原因
        previewFrameTexture.updateTexImage();
    }


    private void setupPreviewDisplayView() {
        previewDisplayView.setVisibility(View.GONE);
        ViewGroup viewGroup = findViewById(R.id.preview_display_layout);
        viewGroup.addView(previewDisplayView);

        previewDisplayView
                .getHolder()
                .addCallback(
                        new SurfaceHolder.Callback() {
                            @Override
                            public void surfaceCreated(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(holder.getSurface());

                            }

                            @Override
                            public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
                                onPreviewDisplaySurfaceChanged(holder, format, width, height);
                            }

                            @Override
                            public void surfaceDestroyed(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(null);
                            }
                        });
    }
}